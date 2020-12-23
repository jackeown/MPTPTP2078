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
% DateTime   : Thu Dec  3 11:59:03 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  149 (1101 expanded)
%              Number of clauses        :   81 ( 324 expanded)
%              Number of leaves         :   18 ( 246 expanded)
%              Depth                    :   22
%              Number of atoms          :  461 (5467 expanded)
%              Number of equality atoms :  312 (3397 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X7
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X7
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f28,f37])).

fof(f64,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f64,f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f33])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f66,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f85,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f78])).

fof(f65,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f65,f46])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f47])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f69,plain,(
    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f83,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f76])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_831,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_842,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3139,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_842])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_231,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_830,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_232])).

cnf(c_3280,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3139,c_830])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_836,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_839,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2147,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK1(k2_zfmisc_1(X0,X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_839])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_846,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4550,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2147,c_846])).

cnf(c_4586,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3280,c_4550])).

cnf(c_21,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4802,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_4586,c_21])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_504,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1024,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1025,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_1026,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1027,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1028,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1029,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_5798,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4802,c_25,c_24,c_23,c_32,c_33,c_1025,c_1027,c_1029])).

cnf(c_5942,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_5798,c_25])).

cnf(c_3279,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3139,c_839])).

cnf(c_3329,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_830])).

cnf(c_2145,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_846])).

cnf(c_5106,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3329,c_2145])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ m1_subset_1(X1,sK3)
    | ~ m1_subset_1(X2,sK2)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK6
    | sK5 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_832,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
    | sK5 = X2
    | m1_subset_1(X2,sK4) != iProver_top
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6239,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK5 = X0
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5106,c_832])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_840,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3327,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_840])).

cnf(c_4244,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_2145])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_843,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5134,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4244,c_843])).

cnf(c_3328,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_839])).

cnf(c_4693,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_2145])).

cnf(c_5149,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4693,c_843])).

cnf(c_6443,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK5 = X0
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6239,c_5134,c_5149])).

cnf(c_6453,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k2_mcart_1(sK6) = sK5
    | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5942,c_6443])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_835,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3374,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_831,c_835])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,X1),X2))
    | k7_mcart_1(sK2,X1,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X1))
    | k7_mcart_1(sK2,sK3,X1,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1802,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k7_mcart_1(sK2,sK3,sK4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_3170,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_4159,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3374,c_27,c_25,c_24,c_23,c_3170])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_841,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2977,plain,
    ( m1_subset_1(k7_mcart_1(sK2,sK3,sK4,sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_841])).

cnf(c_4163,plain,
    ( m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4159,c_2977])).

cnf(c_22,negated_conjecture,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4164,plain,
    ( k2_mcart_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_4159,c_22])).

cnf(c_6456,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6453,c_4163,c_4164])).

cnf(c_6482,plain,
    ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6456,c_835])).

cnf(c_18,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1287,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18,c_18])).

cnf(c_6589,plain,
    ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6482,c_1287])).

cnf(c_6497,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_6456,c_21])).

cnf(c_6515,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6497,c_1287])).

cnf(c_6516,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6515])).

cnf(c_8709,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6589,c_25,c_24,c_23,c_32,c_33,c_1025,c_1027,c_1029,c_6516])).

cnf(c_8782,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8709,c_23])).

cnf(c_8802,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:56:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.36/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/0.94  
% 3.36/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.94  
% 3.36/0.94  ------  iProver source info
% 3.36/0.94  
% 3.36/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.94  git: non_committed_changes: false
% 3.36/0.94  git: last_make_outside_of_git: false
% 3.36/0.94  
% 3.36/0.94  ------ 
% 3.36/0.94  
% 3.36/0.94  ------ Input Options
% 3.36/0.94  
% 3.36/0.94  --out_options                           all
% 3.36/0.94  --tptp_safe_out                         true
% 3.36/0.94  --problem_path                          ""
% 3.36/0.94  --include_path                          ""
% 3.36/0.94  --clausifier                            res/vclausify_rel
% 3.36/0.94  --clausifier_options                    --mode clausify
% 3.36/0.94  --stdin                                 false
% 3.36/0.94  --stats_out                             all
% 3.36/0.94  
% 3.36/0.94  ------ General Options
% 3.36/0.94  
% 3.36/0.94  --fof                                   false
% 3.36/0.94  --time_out_real                         305.
% 3.36/0.94  --time_out_virtual                      -1.
% 3.36/0.94  --symbol_type_check                     false
% 3.36/0.94  --clausify_out                          false
% 3.36/0.94  --sig_cnt_out                           false
% 3.36/0.94  --trig_cnt_out                          false
% 3.36/0.94  --trig_cnt_out_tolerance                1.
% 3.36/0.94  --trig_cnt_out_sk_spl                   false
% 3.36/0.94  --abstr_cl_out                          false
% 3.36/0.94  
% 3.36/0.94  ------ Global Options
% 3.36/0.94  
% 3.36/0.94  --schedule                              default
% 3.36/0.94  --add_important_lit                     false
% 3.36/0.94  --prop_solver_per_cl                    1000
% 3.36/0.94  --min_unsat_core                        false
% 3.36/0.94  --soft_assumptions                      false
% 3.36/0.94  --soft_lemma_size                       3
% 3.36/0.94  --prop_impl_unit_size                   0
% 3.36/0.94  --prop_impl_unit                        []
% 3.36/0.94  --share_sel_clauses                     true
% 3.36/0.94  --reset_solvers                         false
% 3.36/0.94  --bc_imp_inh                            [conj_cone]
% 3.36/0.94  --conj_cone_tolerance                   3.
% 3.36/0.94  --extra_neg_conj                        none
% 3.36/0.94  --large_theory_mode                     true
% 3.36/0.94  --prolific_symb_bound                   200
% 3.36/0.94  --lt_threshold                          2000
% 3.36/0.94  --clause_weak_htbl                      true
% 3.36/0.94  --gc_record_bc_elim                     false
% 3.36/0.94  
% 3.36/0.94  ------ Preprocessing Options
% 3.36/0.94  
% 3.36/0.94  --preprocessing_flag                    true
% 3.36/0.94  --time_out_prep_mult                    0.1
% 3.36/0.94  --splitting_mode                        input
% 3.36/0.94  --splitting_grd                         true
% 3.36/0.94  --splitting_cvd                         false
% 3.36/0.94  --splitting_cvd_svl                     false
% 3.36/0.94  --splitting_nvd                         32
% 3.36/0.94  --sub_typing                            true
% 3.36/0.94  --prep_gs_sim                           true
% 3.36/0.94  --prep_unflatten                        true
% 3.36/0.94  --prep_res_sim                          true
% 3.36/0.94  --prep_upred                            true
% 3.36/0.94  --prep_sem_filter                       exhaustive
% 3.36/0.94  --prep_sem_filter_out                   false
% 3.36/0.94  --pred_elim                             true
% 3.36/0.94  --res_sim_input                         true
% 3.36/0.94  --eq_ax_congr_red                       true
% 3.36/0.94  --pure_diseq_elim                       true
% 3.36/0.94  --brand_transform                       false
% 3.36/0.94  --non_eq_to_eq                          false
% 3.36/0.94  --prep_def_merge                        true
% 3.36/0.94  --prep_def_merge_prop_impl              false
% 3.36/0.94  --prep_def_merge_mbd                    true
% 3.36/0.94  --prep_def_merge_tr_red                 false
% 3.36/0.94  --prep_def_merge_tr_cl                  false
% 3.36/0.94  --smt_preprocessing                     true
% 3.36/0.94  --smt_ac_axioms                         fast
% 3.36/0.94  --preprocessed_out                      false
% 3.36/0.94  --preprocessed_stats                    false
% 3.36/0.94  
% 3.36/0.94  ------ Abstraction refinement Options
% 3.36/0.94  
% 3.36/0.94  --abstr_ref                             []
% 3.36/0.94  --abstr_ref_prep                        false
% 3.36/0.94  --abstr_ref_until_sat                   false
% 3.36/0.94  --abstr_ref_sig_restrict                funpre
% 3.36/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.94  --abstr_ref_under                       []
% 3.36/0.94  
% 3.36/0.94  ------ SAT Options
% 3.36/0.94  
% 3.36/0.94  --sat_mode                              false
% 3.36/0.94  --sat_fm_restart_options                ""
% 3.36/0.94  --sat_gr_def                            false
% 3.36/0.94  --sat_epr_types                         true
% 3.36/0.94  --sat_non_cyclic_types                  false
% 3.36/0.94  --sat_finite_models                     false
% 3.36/0.94  --sat_fm_lemmas                         false
% 3.36/0.94  --sat_fm_prep                           false
% 3.36/0.94  --sat_fm_uc_incr                        true
% 3.36/0.94  --sat_out_model                         small
% 3.36/0.94  --sat_out_clauses                       false
% 3.36/0.94  
% 3.36/0.94  ------ QBF Options
% 3.36/0.94  
% 3.36/0.94  --qbf_mode                              false
% 3.36/0.94  --qbf_elim_univ                         false
% 3.36/0.94  --qbf_dom_inst                          none
% 3.36/0.94  --qbf_dom_pre_inst                      false
% 3.36/0.94  --qbf_sk_in                             false
% 3.36/0.94  --qbf_pred_elim                         true
% 3.36/0.94  --qbf_split                             512
% 3.36/0.94  
% 3.36/0.94  ------ BMC1 Options
% 3.36/0.94  
% 3.36/0.94  --bmc1_incremental                      false
% 3.36/0.94  --bmc1_axioms                           reachable_all
% 3.36/0.94  --bmc1_min_bound                        0
% 3.36/0.94  --bmc1_max_bound                        -1
% 3.36/0.94  --bmc1_max_bound_default                -1
% 3.36/0.94  --bmc1_symbol_reachability              true
% 3.36/0.94  --bmc1_property_lemmas                  false
% 3.36/0.94  --bmc1_k_induction                      false
% 3.36/0.94  --bmc1_non_equiv_states                 false
% 3.36/0.94  --bmc1_deadlock                         false
% 3.36/0.94  --bmc1_ucm                              false
% 3.36/0.94  --bmc1_add_unsat_core                   none
% 3.36/0.94  --bmc1_unsat_core_children              false
% 3.36/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.94  --bmc1_out_stat                         full
% 3.36/0.94  --bmc1_ground_init                      false
% 3.36/0.94  --bmc1_pre_inst_next_state              false
% 3.36/0.94  --bmc1_pre_inst_state                   false
% 3.36/0.94  --bmc1_pre_inst_reach_state             false
% 3.36/0.94  --bmc1_out_unsat_core                   false
% 3.36/0.94  --bmc1_aig_witness_out                  false
% 3.36/0.94  --bmc1_verbose                          false
% 3.36/0.94  --bmc1_dump_clauses_tptp                false
% 3.36/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.94  --bmc1_dump_file                        -
% 3.36/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.94  --bmc1_ucm_extend_mode                  1
% 3.36/0.94  --bmc1_ucm_init_mode                    2
% 3.36/0.94  --bmc1_ucm_cone_mode                    none
% 3.36/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.94  --bmc1_ucm_relax_model                  4
% 3.36/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.94  --bmc1_ucm_layered_model                none
% 3.36/0.94  --bmc1_ucm_max_lemma_size               10
% 3.36/0.94  
% 3.36/0.94  ------ AIG Options
% 3.36/0.94  
% 3.36/0.94  --aig_mode                              false
% 3.36/0.94  
% 3.36/0.94  ------ Instantiation Options
% 3.36/0.94  
% 3.36/0.94  --instantiation_flag                    true
% 3.36/0.94  --inst_sos_flag                         false
% 3.36/0.94  --inst_sos_phase                        true
% 3.36/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.94  --inst_lit_sel_side                     num_symb
% 3.36/0.94  --inst_solver_per_active                1400
% 3.36/0.94  --inst_solver_calls_frac                1.
% 3.36/0.94  --inst_passive_queue_type               priority_queues
% 3.36/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.94  --inst_passive_queues_freq              [25;2]
% 3.36/0.94  --inst_dismatching                      true
% 3.36/0.94  --inst_eager_unprocessed_to_passive     true
% 3.36/0.94  --inst_prop_sim_given                   true
% 3.36/0.94  --inst_prop_sim_new                     false
% 3.36/0.94  --inst_subs_new                         false
% 3.36/0.94  --inst_eq_res_simp                      false
% 3.36/0.94  --inst_subs_given                       false
% 3.36/0.94  --inst_orphan_elimination               true
% 3.36/0.94  --inst_learning_loop_flag               true
% 3.36/0.94  --inst_learning_start                   3000
% 3.36/0.94  --inst_learning_factor                  2
% 3.36/0.94  --inst_start_prop_sim_after_learn       3
% 3.36/0.94  --inst_sel_renew                        solver
% 3.36/0.94  --inst_lit_activity_flag                true
% 3.36/0.94  --inst_restr_to_given                   false
% 3.36/0.94  --inst_activity_threshold               500
% 3.36/0.94  --inst_out_proof                        true
% 3.36/0.94  
% 3.36/0.94  ------ Resolution Options
% 3.36/0.94  
% 3.36/0.94  --resolution_flag                       true
% 3.36/0.94  --res_lit_sel                           adaptive
% 3.36/0.94  --res_lit_sel_side                      none
% 3.36/0.94  --res_ordering                          kbo
% 3.36/0.94  --res_to_prop_solver                    active
% 3.36/0.94  --res_prop_simpl_new                    false
% 3.36/0.94  --res_prop_simpl_given                  true
% 3.36/0.94  --res_passive_queue_type                priority_queues
% 3.36/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.94  --res_passive_queues_freq               [15;5]
% 3.36/0.94  --res_forward_subs                      full
% 3.36/0.94  --res_backward_subs                     full
% 3.36/0.94  --res_forward_subs_resolution           true
% 3.36/0.94  --res_backward_subs_resolution          true
% 3.36/0.94  --res_orphan_elimination                true
% 3.36/0.94  --res_time_limit                        2.
% 3.36/0.94  --res_out_proof                         true
% 3.36/0.94  
% 3.36/0.94  ------ Superposition Options
% 3.36/0.94  
% 3.36/0.94  --superposition_flag                    true
% 3.36/0.94  --sup_passive_queue_type                priority_queues
% 3.36/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.94  --demod_completeness_check              fast
% 3.36/0.94  --demod_use_ground                      true
% 3.36/0.94  --sup_to_prop_solver                    passive
% 3.36/0.94  --sup_prop_simpl_new                    true
% 3.36/0.94  --sup_prop_simpl_given                  true
% 3.36/0.94  --sup_fun_splitting                     false
% 3.36/0.94  --sup_smt_interval                      50000
% 3.36/0.94  
% 3.36/0.94  ------ Superposition Simplification Setup
% 3.36/0.94  
% 3.36/0.94  --sup_indices_passive                   []
% 3.36/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.94  --sup_full_bw                           [BwDemod]
% 3.36/0.94  --sup_immed_triv                        [TrivRules]
% 3.36/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.94  --sup_immed_bw_main                     []
% 3.36/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.94  
% 3.36/0.94  ------ Combination Options
% 3.36/0.94  
% 3.36/0.94  --comb_res_mult                         3
% 3.36/0.94  --comb_sup_mult                         2
% 3.36/0.94  --comb_inst_mult                        10
% 3.36/0.94  
% 3.36/0.94  ------ Debug Options
% 3.36/0.94  
% 3.36/0.94  --dbg_backtrace                         false
% 3.36/0.94  --dbg_dump_prop_clauses                 false
% 3.36/0.94  --dbg_dump_prop_clauses_file            -
% 3.36/0.94  --dbg_out_stat                          false
% 3.36/0.94  ------ Parsing...
% 3.36/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.94  
% 3.36/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.36/0.94  
% 3.36/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.94  
% 3.36/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.94  ------ Proving...
% 3.36/0.94  ------ Problem Properties 
% 3.36/0.94  
% 3.36/0.94  
% 3.36/0.94  clauses                                 27
% 3.36/0.94  conjectures                             6
% 3.36/0.94  EPR                                     7
% 3.36/0.94  Horn                                    20
% 3.36/0.94  unary                                   11
% 3.36/0.94  binary                                  8
% 3.36/0.94  lits                                    61
% 3.36/0.94  lits eq                                 33
% 3.36/0.94  fd_pure                                 0
% 3.36/0.94  fd_pseudo                               0
% 3.36/0.94  fd_cond                                 8
% 3.36/0.94  fd_pseudo_cond                          0
% 3.36/0.94  AC symbols                              0
% 3.36/0.94  
% 3.36/0.94  ------ Schedule dynamic 5 is on 
% 3.36/0.94  
% 3.36/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/0.94  
% 3.36/0.94  
% 3.36/0.94  ------ 
% 3.36/0.94  Current options:
% 3.36/0.94  ------ 
% 3.36/0.94  
% 3.36/0.94  ------ Input Options
% 3.36/0.94  
% 3.36/0.94  --out_options                           all
% 3.36/0.94  --tptp_safe_out                         true
% 3.36/0.94  --problem_path                          ""
% 3.36/0.94  --include_path                          ""
% 3.36/0.94  --clausifier                            res/vclausify_rel
% 3.36/0.94  --clausifier_options                    --mode clausify
% 3.36/0.94  --stdin                                 false
% 3.36/0.94  --stats_out                             all
% 3.36/0.94  
% 3.36/0.94  ------ General Options
% 3.36/0.94  
% 3.36/0.94  --fof                                   false
% 3.36/0.94  --time_out_real                         305.
% 3.36/0.94  --time_out_virtual                      -1.
% 3.36/0.94  --symbol_type_check                     false
% 3.36/0.94  --clausify_out                          false
% 3.36/0.94  --sig_cnt_out                           false
% 3.36/0.94  --trig_cnt_out                          false
% 3.36/0.94  --trig_cnt_out_tolerance                1.
% 3.36/0.94  --trig_cnt_out_sk_spl                   false
% 3.36/0.94  --abstr_cl_out                          false
% 3.36/0.94  
% 3.36/0.94  ------ Global Options
% 3.36/0.94  
% 3.36/0.94  --schedule                              default
% 3.36/0.94  --add_important_lit                     false
% 3.36/0.94  --prop_solver_per_cl                    1000
% 3.36/0.94  --min_unsat_core                        false
% 3.36/0.94  --soft_assumptions                      false
% 3.36/0.94  --soft_lemma_size                       3
% 3.36/0.94  --prop_impl_unit_size                   0
% 3.36/0.94  --prop_impl_unit                        []
% 3.36/0.94  --share_sel_clauses                     true
% 3.36/0.94  --reset_solvers                         false
% 3.36/0.94  --bc_imp_inh                            [conj_cone]
% 3.36/0.94  --conj_cone_tolerance                   3.
% 3.36/0.94  --extra_neg_conj                        none
% 3.36/0.94  --large_theory_mode                     true
% 3.36/0.94  --prolific_symb_bound                   200
% 3.36/0.94  --lt_threshold                          2000
% 3.36/0.94  --clause_weak_htbl                      true
% 3.36/0.94  --gc_record_bc_elim                     false
% 3.36/0.94  
% 3.36/0.94  ------ Preprocessing Options
% 3.36/0.94  
% 3.36/0.94  --preprocessing_flag                    true
% 3.36/0.94  --time_out_prep_mult                    0.1
% 3.36/0.94  --splitting_mode                        input
% 3.36/0.94  --splitting_grd                         true
% 3.36/0.94  --splitting_cvd                         false
% 3.36/0.94  --splitting_cvd_svl                     false
% 3.36/0.94  --splitting_nvd                         32
% 3.36/0.94  --sub_typing                            true
% 3.36/0.94  --prep_gs_sim                           true
% 3.36/0.94  --prep_unflatten                        true
% 3.36/0.94  --prep_res_sim                          true
% 3.36/0.94  --prep_upred                            true
% 3.36/0.94  --prep_sem_filter                       exhaustive
% 3.36/0.94  --prep_sem_filter_out                   false
% 3.36/0.94  --pred_elim                             true
% 3.36/0.94  --res_sim_input                         true
% 3.36/0.94  --eq_ax_congr_red                       true
% 3.36/0.94  --pure_diseq_elim                       true
% 3.36/0.94  --brand_transform                       false
% 3.36/0.94  --non_eq_to_eq                          false
% 3.36/0.94  --prep_def_merge                        true
% 3.36/0.94  --prep_def_merge_prop_impl              false
% 3.36/0.94  --prep_def_merge_mbd                    true
% 3.36/0.94  --prep_def_merge_tr_red                 false
% 3.36/0.94  --prep_def_merge_tr_cl                  false
% 3.36/0.94  --smt_preprocessing                     true
% 3.36/0.94  --smt_ac_axioms                         fast
% 3.36/0.94  --preprocessed_out                      false
% 3.36/0.94  --preprocessed_stats                    false
% 3.36/0.94  
% 3.36/0.94  ------ Abstraction refinement Options
% 3.36/0.94  
% 3.36/0.94  --abstr_ref                             []
% 3.36/0.94  --abstr_ref_prep                        false
% 3.36/0.94  --abstr_ref_until_sat                   false
% 3.36/0.94  --abstr_ref_sig_restrict                funpre
% 3.36/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.94  --abstr_ref_under                       []
% 3.36/0.94  
% 3.36/0.94  ------ SAT Options
% 3.36/0.94  
% 3.36/0.94  --sat_mode                              false
% 3.36/0.94  --sat_fm_restart_options                ""
% 3.36/0.94  --sat_gr_def                            false
% 3.36/0.94  --sat_epr_types                         true
% 3.36/0.94  --sat_non_cyclic_types                  false
% 3.36/0.94  --sat_finite_models                     false
% 3.36/0.94  --sat_fm_lemmas                         false
% 3.36/0.94  --sat_fm_prep                           false
% 3.36/0.94  --sat_fm_uc_incr                        true
% 3.36/0.94  --sat_out_model                         small
% 3.36/0.94  --sat_out_clauses                       false
% 3.36/0.94  
% 3.36/0.94  ------ QBF Options
% 3.36/0.94  
% 3.36/0.94  --qbf_mode                              false
% 3.36/0.94  --qbf_elim_univ                         false
% 3.36/0.94  --qbf_dom_inst                          none
% 3.36/0.94  --qbf_dom_pre_inst                      false
% 3.36/0.94  --qbf_sk_in                             false
% 3.36/0.94  --qbf_pred_elim                         true
% 3.36/0.94  --qbf_split                             512
% 3.36/0.94  
% 3.36/0.94  ------ BMC1 Options
% 3.36/0.94  
% 3.36/0.94  --bmc1_incremental                      false
% 3.36/0.94  --bmc1_axioms                           reachable_all
% 3.36/0.94  --bmc1_min_bound                        0
% 3.36/0.94  --bmc1_max_bound                        -1
% 3.36/0.94  --bmc1_max_bound_default                -1
% 3.36/0.94  --bmc1_symbol_reachability              true
% 3.36/0.94  --bmc1_property_lemmas                  false
% 3.36/0.94  --bmc1_k_induction                      false
% 3.36/0.94  --bmc1_non_equiv_states                 false
% 3.36/0.94  --bmc1_deadlock                         false
% 3.36/0.94  --bmc1_ucm                              false
% 3.36/0.94  --bmc1_add_unsat_core                   none
% 3.36/0.94  --bmc1_unsat_core_children              false
% 3.36/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.94  --bmc1_out_stat                         full
% 3.36/0.94  --bmc1_ground_init                      false
% 3.36/0.94  --bmc1_pre_inst_next_state              false
% 3.36/0.94  --bmc1_pre_inst_state                   false
% 3.36/0.94  --bmc1_pre_inst_reach_state             false
% 3.36/0.94  --bmc1_out_unsat_core                   false
% 3.36/0.94  --bmc1_aig_witness_out                  false
% 3.36/0.94  --bmc1_verbose                          false
% 3.36/0.94  --bmc1_dump_clauses_tptp                false
% 3.36/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.94  --bmc1_dump_file                        -
% 3.36/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.94  --bmc1_ucm_extend_mode                  1
% 3.36/0.94  --bmc1_ucm_init_mode                    2
% 3.36/0.94  --bmc1_ucm_cone_mode                    none
% 3.36/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.94  --bmc1_ucm_relax_model                  4
% 3.36/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.94  --bmc1_ucm_layered_model                none
% 3.36/0.94  --bmc1_ucm_max_lemma_size               10
% 3.36/0.94  
% 3.36/0.94  ------ AIG Options
% 3.36/0.94  
% 3.36/0.94  --aig_mode                              false
% 3.36/0.94  
% 3.36/0.94  ------ Instantiation Options
% 3.36/0.94  
% 3.36/0.94  --instantiation_flag                    true
% 3.36/0.94  --inst_sos_flag                         false
% 3.36/0.94  --inst_sos_phase                        true
% 3.36/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.94  --inst_lit_sel_side                     none
% 3.36/0.94  --inst_solver_per_active                1400
% 3.36/0.94  --inst_solver_calls_frac                1.
% 3.36/0.94  --inst_passive_queue_type               priority_queues
% 3.36/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.94  --inst_passive_queues_freq              [25;2]
% 3.36/0.94  --inst_dismatching                      true
% 3.36/0.94  --inst_eager_unprocessed_to_passive     true
% 3.36/0.94  --inst_prop_sim_given                   true
% 3.36/0.94  --inst_prop_sim_new                     false
% 3.36/0.94  --inst_subs_new                         false
% 3.36/0.94  --inst_eq_res_simp                      false
% 3.36/0.94  --inst_subs_given                       false
% 3.36/0.94  --inst_orphan_elimination               true
% 3.36/0.94  --inst_learning_loop_flag               true
% 3.36/0.94  --inst_learning_start                   3000
% 3.36/0.94  --inst_learning_factor                  2
% 3.36/0.94  --inst_start_prop_sim_after_learn       3
% 3.36/0.94  --inst_sel_renew                        solver
% 3.36/0.94  --inst_lit_activity_flag                true
% 3.36/0.94  --inst_restr_to_given                   false
% 3.36/0.94  --inst_activity_threshold               500
% 3.36/0.94  --inst_out_proof                        true
% 3.36/0.94  
% 3.36/0.94  ------ Resolution Options
% 3.36/0.94  
% 3.36/0.94  --resolution_flag                       false
% 3.36/0.94  --res_lit_sel                           adaptive
% 3.36/0.94  --res_lit_sel_side                      none
% 3.36/0.94  --res_ordering                          kbo
% 3.36/0.94  --res_to_prop_solver                    active
% 3.36/0.94  --res_prop_simpl_new                    false
% 3.36/0.94  --res_prop_simpl_given                  true
% 3.36/0.94  --res_passive_queue_type                priority_queues
% 3.36/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.94  --res_passive_queues_freq               [15;5]
% 3.36/0.94  --res_forward_subs                      full
% 3.36/0.94  --res_backward_subs                     full
% 3.36/0.94  --res_forward_subs_resolution           true
% 3.36/0.94  --res_backward_subs_resolution          true
% 3.36/0.94  --res_orphan_elimination                true
% 3.36/0.94  --res_time_limit                        2.
% 3.36/0.94  --res_out_proof                         true
% 3.36/0.94  
% 3.36/0.94  ------ Superposition Options
% 3.36/0.94  
% 3.36/0.94  --superposition_flag                    true
% 3.36/0.94  --sup_passive_queue_type                priority_queues
% 3.36/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.94  --demod_completeness_check              fast
% 3.36/0.94  --demod_use_ground                      true
% 3.36/0.94  --sup_to_prop_solver                    passive
% 3.36/0.94  --sup_prop_simpl_new                    true
% 3.36/0.94  --sup_prop_simpl_given                  true
% 3.36/0.94  --sup_fun_splitting                     false
% 3.36/0.94  --sup_smt_interval                      50000
% 3.36/0.94  
% 3.36/0.94  ------ Superposition Simplification Setup
% 3.36/0.94  
% 3.36/0.94  --sup_indices_passive                   []
% 3.36/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.94  --sup_full_bw                           [BwDemod]
% 3.36/0.94  --sup_immed_triv                        [TrivRules]
% 3.36/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.94  --sup_immed_bw_main                     []
% 3.36/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.94  
% 3.36/0.94  ------ Combination Options
% 3.36/0.94  
% 3.36/0.94  --comb_res_mult                         3
% 3.36/0.94  --comb_sup_mult                         2
% 3.36/0.94  --comb_inst_mult                        10
% 3.36/0.94  
% 3.36/0.94  ------ Debug Options
% 3.36/0.94  
% 3.36/0.94  --dbg_backtrace                         false
% 3.36/0.94  --dbg_dump_prop_clauses                 false
% 3.36/0.94  --dbg_dump_prop_clauses_file            -
% 3.36/0.94  --dbg_out_stat                          false
% 3.36/0.94  
% 3.36/0.94  
% 3.36/0.94  
% 3.36/0.94  
% 3.36/0.94  ------ Proving...
% 3.36/0.94  
% 3.36/0.94  
% 3.36/0.94  % SZS status Theorem for theBenchmark.p
% 3.36/0.94  
% 3.36/0.94   Resolution empty clause
% 3.36/0.94  
% 3.36/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/0.94  
% 3.36/0.94  fof(f16,conjecture,(
% 3.36/0.94    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.36/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.94  
% 3.36/0.94  fof(f17,negated_conjecture,(
% 3.36/0.94    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.36/0.94    inference(negated_conjecture,[],[f16])).
% 3.36/0.94  
% 3.36/0.94  fof(f27,plain,(
% 3.36/0.94    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/0.94    inference(ennf_transformation,[],[f17])).
% 3.36/0.94  
% 3.36/0.94  fof(f28,plain,(
% 3.36/0.94    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/0.94    inference(flattening,[],[f27])).
% 3.36/0.94  
% 3.36/0.94  fof(f37,plain,(
% 3.36/0.94    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 3.36/0.94    introduced(choice_axiom,[])).
% 3.36/0.94  
% 3.36/0.94  fof(f38,plain,(
% 3.36/0.94    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.36/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f28,f37])).
% 3.36/0.94  
% 3.36/0.94  fof(f64,plain,(
% 3.36/0.94    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.36/0.94    inference(cnf_transformation,[],[f38])).
% 3.36/0.94  
% 3.36/0.94  fof(f8,axiom,(
% 3.36/0.94    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.36/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.94  
% 3.36/0.94  fof(f47,plain,(
% 3.36/0.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.36/0.94    inference(cnf_transformation,[],[f8])).
% 3.36/0.94  
% 3.36/0.94  fof(f81,plain,(
% 3.36/0.94    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 3.36/0.94    inference(definition_unfolding,[],[f64,f47])).
% 3.36/0.94  
% 3.36/0.94  fof(f5,axiom,(
% 3.36/0.94    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f19,plain,(
% 3.36/0.95    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.36/0.95    inference(ennf_transformation,[],[f5])).
% 3.36/0.95  
% 3.36/0.95  fof(f20,plain,(
% 3.36/0.95    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.36/0.95    inference(flattening,[],[f19])).
% 3.36/0.95  
% 3.36/0.95  fof(f44,plain,(
% 3.36/0.95    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f20])).
% 3.36/0.95  
% 3.36/0.95  fof(f6,axiom,(
% 3.36/0.95    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f45,plain,(
% 3.36/0.95    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.36/0.95    inference(cnf_transformation,[],[f6])).
% 3.36/0.95  
% 3.36/0.95  fof(f12,axiom,(
% 3.36/0.95    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f23,plain,(
% 3.36/0.95    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.36/0.95    inference(ennf_transformation,[],[f12])).
% 3.36/0.95  
% 3.36/0.95  fof(f24,plain,(
% 3.36/0.95    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.36/0.95    inference(flattening,[],[f23])).
% 3.36/0.95  
% 3.36/0.95  fof(f52,plain,(
% 3.36/0.95    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f24])).
% 3.36/0.95  
% 3.36/0.95  fof(f13,axiom,(
% 3.36/0.95    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f25,plain,(
% 3.36/0.95    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.36/0.95    inference(ennf_transformation,[],[f13])).
% 3.36/0.95  
% 3.36/0.95  fof(f33,plain,(
% 3.36/0.95    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 3.36/0.95    introduced(choice_axiom,[])).
% 3.36/0.95  
% 3.36/0.95  fof(f34,plain,(
% 3.36/0.95    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 3.36/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f33])).
% 3.36/0.95  
% 3.36/0.95  fof(f53,plain,(
% 3.36/0.95    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.36/0.95    inference(cnf_transformation,[],[f34])).
% 3.36/0.95  
% 3.36/0.95  fof(f11,axiom,(
% 3.36/0.95    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f22,plain,(
% 3.36/0.95    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.36/0.95    inference(ennf_transformation,[],[f11])).
% 3.36/0.95  
% 3.36/0.95  fof(f50,plain,(
% 3.36/0.95    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.36/0.95    inference(cnf_transformation,[],[f22])).
% 3.36/0.95  
% 3.36/0.95  fof(f1,axiom,(
% 3.36/0.95    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f29,plain,(
% 3.36/0.95    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.36/0.95    inference(nnf_transformation,[],[f1])).
% 3.36/0.95  
% 3.36/0.95  fof(f30,plain,(
% 3.36/0.95    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.36/0.95    inference(rectify,[],[f29])).
% 3.36/0.95  
% 3.36/0.95  fof(f31,plain,(
% 3.36/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.36/0.95    introduced(choice_axiom,[])).
% 3.36/0.95  
% 3.36/0.95  fof(f32,plain,(
% 3.36/0.95    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.36/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.36/0.95  
% 3.36/0.95  fof(f39,plain,(
% 3.36/0.95    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f32])).
% 3.36/0.95  
% 3.36/0.95  fof(f15,axiom,(
% 3.36/0.95    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f35,plain,(
% 3.36/0.95    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.36/0.95    inference(nnf_transformation,[],[f15])).
% 3.36/0.95  
% 3.36/0.95  fof(f36,plain,(
% 3.36/0.95    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.36/0.95    inference(flattening,[],[f35])).
% 3.36/0.95  
% 3.36/0.95  fof(f59,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/0.95    inference(cnf_transformation,[],[f36])).
% 3.36/0.95  
% 3.36/0.95  fof(f9,axiom,(
% 3.36/0.95    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f48,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f9])).
% 3.36/0.95  
% 3.36/0.95  fof(f70,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.36/0.95    inference(definition_unfolding,[],[f48,f47])).
% 3.36/0.95  
% 3.36/0.95  fof(f79,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/0.95    inference(definition_unfolding,[],[f59,f70])).
% 3.36/0.95  
% 3.36/0.95  fof(f66,plain,(
% 3.36/0.95    k1_xboole_0 != sK2),
% 3.36/0.95    inference(cnf_transformation,[],[f38])).
% 3.36/0.95  
% 3.36/0.95  fof(f67,plain,(
% 3.36/0.95    k1_xboole_0 != sK3),
% 3.36/0.95    inference(cnf_transformation,[],[f38])).
% 3.36/0.95  
% 3.36/0.95  fof(f68,plain,(
% 3.36/0.95    k1_xboole_0 != sK4),
% 3.36/0.95    inference(cnf_transformation,[],[f38])).
% 3.36/0.95  
% 3.36/0.95  fof(f60,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f36])).
% 3.36/0.95  
% 3.36/0.95  fof(f78,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.36/0.95    inference(definition_unfolding,[],[f60,f70])).
% 3.36/0.95  
% 3.36/0.95  fof(f85,plain,(
% 3.36/0.95    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 3.36/0.95    inference(equality_resolution,[],[f78])).
% 3.36/0.95  
% 3.36/0.95  fof(f65,plain,(
% 3.36/0.95    ( ! [X6,X7,X5] : (sK5 = X7 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f38])).
% 3.36/0.95  
% 3.36/0.95  fof(f7,axiom,(
% 3.36/0.95    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f46,plain,(
% 3.36/0.95    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f7])).
% 3.36/0.95  
% 3.36/0.95  fof(f80,plain,(
% 3.36/0.95    ( ! [X6,X7,X5] : (sK5 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.36/0.95    inference(definition_unfolding,[],[f65,f46])).
% 3.36/0.95  
% 3.36/0.95  fof(f51,plain,(
% 3.36/0.95    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.36/0.95    inference(cnf_transformation,[],[f22])).
% 3.36/0.95  
% 3.36/0.95  fof(f4,axiom,(
% 3.36/0.95    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f18,plain,(
% 3.36/0.95    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.36/0.95    inference(ennf_transformation,[],[f4])).
% 3.36/0.95  
% 3.36/0.95  fof(f43,plain,(
% 3.36/0.95    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f18])).
% 3.36/0.95  
% 3.36/0.95  fof(f14,axiom,(
% 3.36/0.95    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f26,plain,(
% 3.36/0.95    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.36/0.95    inference(ennf_transformation,[],[f14])).
% 3.36/0.95  
% 3.36/0.95  fof(f58,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/0.95    inference(cnf_transformation,[],[f26])).
% 3.36/0.95  
% 3.36/0.95  fof(f72,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.36/0.95    inference(definition_unfolding,[],[f58,f47])).
% 3.36/0.95  
% 3.36/0.95  fof(f10,axiom,(
% 3.36/0.95    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.36/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.36/0.95  
% 3.36/0.95  fof(f21,plain,(
% 3.36/0.95    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.36/0.95    inference(ennf_transformation,[],[f10])).
% 3.36/0.95  
% 3.36/0.95  fof(f49,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.36/0.95    inference(cnf_transformation,[],[f21])).
% 3.36/0.95  
% 3.36/0.95  fof(f71,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.36/0.95    inference(definition_unfolding,[],[f49,f47])).
% 3.36/0.95  
% 3.36/0.95  fof(f69,plain,(
% 3.36/0.95    k7_mcart_1(sK2,sK3,sK4,sK6) != sK5),
% 3.36/0.95    inference(cnf_transformation,[],[f38])).
% 3.36/0.95  
% 3.36/0.95  fof(f62,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.36/0.95    inference(cnf_transformation,[],[f36])).
% 3.36/0.95  
% 3.36/0.95  fof(f76,plain,(
% 3.36/0.95    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.36/0.95    inference(definition_unfolding,[],[f62,f70])).
% 3.36/0.95  
% 3.36/0.95  fof(f83,plain,(
% 3.36/0.95    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 3.36/0.95    inference(equality_resolution,[],[f76])).
% 3.36/0.95  
% 3.36/0.95  cnf(c_27,negated_conjecture,
% 3.36/0.95      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 3.36/0.95      inference(cnf_transformation,[],[f81]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_831,plain,
% 3.36/0.95      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_5,plain,
% 3.36/0.95      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.36/0.95      inference(cnf_transformation,[],[f44]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_842,plain,
% 3.36/0.95      ( m1_subset_1(X0,X1) != iProver_top
% 3.36/0.95      | r2_hidden(X0,X1) = iProver_top
% 3.36/0.95      | v1_xboole_0(X1) = iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3139,plain,
% 3.36/0.95      ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
% 3.36/0.95      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_831,c_842]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6,plain,
% 3.36/0.95      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.36/0.95      inference(cnf_transformation,[],[f45]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_10,plain,
% 3.36/0.95      ( ~ r2_hidden(X0,X1)
% 3.36/0.95      | ~ v1_relat_1(X1)
% 3.36/0.95      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.36/0.95      inference(cnf_transformation,[],[f52]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_231,plain,
% 3.36/0.95      ( ~ r2_hidden(X0,X1)
% 3.36/0.95      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.36/0.95      | k2_zfmisc_1(X2,X3) != X1 ),
% 3.36/0.95      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_232,plain,
% 3.36/0.95      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.36/0.95      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.36/0.95      inference(unflattening,[status(thm)],[c_231]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_830,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.36/0.95      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_232]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3280,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.36/0.95      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3139,c_830]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_13,plain,
% 3.36/0.95      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.36/0.95      inference(cnf_transformation,[],[f53]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_836,plain,
% 3.36/0.95      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_9,plain,
% 3.36/0.95      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.36/0.95      inference(cnf_transformation,[],[f50]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_839,plain,
% 3.36/0.95      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.36/0.95      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_2147,plain,
% 3.36/0.95      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.36/0.95      | r2_hidden(k1_mcart_1(sK1(k2_zfmisc_1(X0,X1))),X0) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_836,c_839]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1,plain,
% 3.36/0.95      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.36/0.95      inference(cnf_transformation,[],[f39]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_846,plain,
% 3.36/0.95      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4550,plain,
% 3.36/0.95      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_2147,c_846]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4586,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.36/0.95      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),X0) = k1_xboole_0 ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3280,c_4550]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_21,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = X0
% 3.36/0.95      | k1_xboole_0 = X2
% 3.36/0.95      | k1_xboole_0 = X1
% 3.36/0.95      | k1_xboole_0 = X3 ),
% 3.36/0.95      inference(cnf_transformation,[],[f79]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4802,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.36/0.95      | sK4 = k1_xboole_0
% 3.36/0.95      | sK3 = k1_xboole_0
% 3.36/0.95      | sK2 = k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = X0 ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_4586,c_21]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_25,negated_conjecture,
% 3.36/0.95      ( k1_xboole_0 != sK2 ),
% 3.36/0.95      inference(cnf_transformation,[],[f66]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_24,negated_conjecture,
% 3.36/0.95      ( k1_xboole_0 != sK3 ),
% 3.36/0.95      inference(cnf_transformation,[],[f67]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_23,negated_conjecture,
% 3.36/0.95      ( k1_xboole_0 != sK4 ),
% 3.36/0.95      inference(cnf_transformation,[],[f68]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_32,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = k1_xboole_0 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_21]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_20,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.36/0.95      inference(cnf_transformation,[],[f85]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_33,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_20]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_504,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1024,plain,
% 3.36/0.95      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_504]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1025,plain,
% 3.36/0.95      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_1024]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1026,plain,
% 3.36/0.95      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_504]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1027,plain,
% 3.36/0.95      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_1026]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1028,plain,
% 3.36/0.95      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_504]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1029,plain,
% 3.36/0.95      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_1028]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_5798,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 | k1_xboole_0 = X0 ),
% 3.36/0.95      inference(global_propositional_subsumption,
% 3.36/0.95                [status(thm)],
% 3.36/0.95                [c_4802,c_25,c_24,c_23,c_32,c_33,c_1025,c_1027,c_1029]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_5942,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_5798,c_25]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3279,plain,
% 3.36/0.95      ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 3.36/0.95      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3139,c_839]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3329,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.36/0.95      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3279,c_830]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_2145,plain,
% 3.36/0.95      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_836,c_846]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_5106,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.36/0.95      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3329,c_2145]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_26,negated_conjecture,
% 3.36/0.95      ( ~ m1_subset_1(X0,sK4)
% 3.36/0.95      | ~ m1_subset_1(X1,sK3)
% 3.36/0.95      | ~ m1_subset_1(X2,sK2)
% 3.36/0.95      | k4_tarski(k4_tarski(X2,X1),X0) != sK6
% 3.36/0.95      | sK5 = X0 ),
% 3.36/0.95      inference(cnf_transformation,[],[f80]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_832,plain,
% 3.36/0.95      ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
% 3.36/0.95      | sK5 = X2
% 3.36/0.95      | m1_subset_1(X2,sK4) != iProver_top
% 3.36/0.95      | m1_subset_1(X1,sK3) != iProver_top
% 3.36/0.95      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6239,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 3.36/0.95      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.36/0.95      | sK5 = X0
% 3.36/0.95      | m1_subset_1(X0,sK4) != iProver_top
% 3.36/0.95      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
% 3.36/0.95      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_5106,c_832]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_8,plain,
% 3.36/0.95      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.36/0.95      inference(cnf_transformation,[],[f51]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_840,plain,
% 3.36/0.95      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.36/0.95      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3327,plain,
% 3.36/0.95      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
% 3.36/0.95      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3279,c_840]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4244,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.36/0.95      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3327,c_2145]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4,plain,
% 3.36/0.95      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.36/0.95      inference(cnf_transformation,[],[f43]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_843,plain,
% 3.36/0.95      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_5134,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.36/0.95      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_4244,c_843]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3328,plain,
% 3.36/0.95      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top
% 3.36/0.95      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3279,c_839]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4693,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.36/0.95      | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_3328,c_2145]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_5149,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.36/0.95      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_4693,c_843]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6443,plain,
% 3.36/0.95      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 3.36/0.95      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.36/0.95      | sK5 = X0
% 3.36/0.95      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.36/0.95      inference(global_propositional_subsumption,
% 3.36/0.95                [status(thm)],
% 3.36/0.95                [c_6239,c_5134,c_5149]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6453,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.36/0.95      | k2_mcart_1(sK6) = sK5
% 3.36/0.95      | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_5942,c_6443]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_14,plain,
% 3.36/0.95      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/0.95      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.36/0.95      | k1_xboole_0 = X1
% 3.36/0.95      | k1_xboole_0 = X3
% 3.36/0.95      | k1_xboole_0 = X2 ),
% 3.36/0.95      inference(cnf_transformation,[],[f72]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_835,plain,
% 3.36/0.95      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.36/0.95      | k1_xboole_0 = X0
% 3.36/0.95      | k1_xboole_0 = X1
% 3.36/0.95      | k1_xboole_0 = X2
% 3.36/0.95      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3374,plain,
% 3.36/0.95      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 3.36/0.95      | sK4 = k1_xboole_0
% 3.36/0.95      | sK3 = k1_xboole_0
% 3.36/0.95      | sK2 = k1_xboole_0 ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_831,c_835]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1088,plain,
% 3.36/0.95      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,X1),X2))
% 3.36/0.95      | k7_mcart_1(sK2,X1,X2,X0) = k2_mcart_1(X0)
% 3.36/0.95      | k1_xboole_0 = X1
% 3.36/0.95      | k1_xboole_0 = X2
% 3.36/0.95      | k1_xboole_0 = sK2 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_14]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1310,plain,
% 3.36/0.95      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X1))
% 3.36/0.95      | k7_mcart_1(sK2,sK3,X1,X0) = k2_mcart_1(X0)
% 3.36/0.95      | k1_xboole_0 = X1
% 3.36/0.95      | k1_xboole_0 = sK3
% 3.36/0.95      | k1_xboole_0 = sK2 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_1088]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1802,plain,
% 3.36/0.95      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 3.36/0.95      | k7_mcart_1(sK2,sK3,sK4,X0) = k2_mcart_1(X0)
% 3.36/0.95      | k1_xboole_0 = sK4
% 3.36/0.95      | k1_xboole_0 = sK3
% 3.36/0.95      | k1_xboole_0 = sK2 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_1310]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_3170,plain,
% 3.36/0.95      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 3.36/0.95      | k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 3.36/0.95      | k1_xboole_0 = sK4
% 3.36/0.95      | k1_xboole_0 = sK3
% 3.36/0.95      | k1_xboole_0 = sK2 ),
% 3.36/0.95      inference(instantiation,[status(thm)],[c_1802]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4159,plain,
% 3.36/0.95      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
% 3.36/0.95      inference(global_propositional_subsumption,
% 3.36/0.95                [status(thm)],
% 3.36/0.95                [c_3374,c_27,c_25,c_24,c_23,c_3170]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_7,plain,
% 3.36/0.95      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.36/0.95      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.36/0.95      inference(cnf_transformation,[],[f71]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_841,plain,
% 3.36/0.95      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.36/0.95      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.36/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_2977,plain,
% 3.36/0.95      ( m1_subset_1(k7_mcart_1(sK2,sK3,sK4,sK6),sK4) = iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_831,c_841]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4163,plain,
% 3.36/0.95      ( m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
% 3.36/0.95      inference(demodulation,[status(thm)],[c_4159,c_2977]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_22,negated_conjecture,
% 3.36/0.95      ( k7_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
% 3.36/0.95      inference(cnf_transformation,[],[f69]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_4164,plain,
% 3.36/0.95      ( k2_mcart_1(sK6) != sK5 ),
% 3.36/0.95      inference(demodulation,[status(thm)],[c_4159,c_22]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6456,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.36/0.95      inference(global_propositional_subsumption,
% 3.36/0.95                [status(thm)],
% 3.36/0.95                [c_6453,c_4163,c_4164]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6482,plain,
% 3.36/0.95      ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
% 3.36/0.95      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.36/0.95      | sK4 = k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = X0
% 3.36/0.95      | m1_subset_1(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_6456,c_835]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_18,plain,
% 3.36/0.95      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 3.36/0.95      inference(cnf_transformation,[],[f83]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_1287,plain,
% 3.36/0.95      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_18,c_18]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6589,plain,
% 3.36/0.95      ( k7_mcart_1(k2_zfmisc_1(sK2,sK3),sK4,X0,X1) = k2_mcart_1(X1)
% 3.36/0.95      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 3.36/0.95      | sK4 = k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = X0
% 3.36/0.95      | m1_subset_1(X1,k1_xboole_0) != iProver_top ),
% 3.36/0.95      inference(light_normalisation,[status(thm)],[c_6482,c_1287]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6497,plain,
% 3.36/0.95      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 3.36/0.95      | sK4 = k1_xboole_0
% 3.36/0.95      | sK3 = k1_xboole_0
% 3.36/0.95      | sK2 = k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = X0 ),
% 3.36/0.95      inference(superposition,[status(thm)],[c_6456,c_21]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6515,plain,
% 3.36/0.95      ( sK4 = k1_xboole_0
% 3.36/0.95      | sK3 = k1_xboole_0
% 3.36/0.95      | sK2 = k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = X0
% 3.36/0.95      | k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.95      inference(light_normalisation,[status(thm)],[c_6497,c_1287]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_6516,plain,
% 3.36/0.95      ( sK4 = k1_xboole_0
% 3.36/0.95      | sK3 = k1_xboole_0
% 3.36/0.95      | sK2 = k1_xboole_0
% 3.36/0.95      | k1_xboole_0 = X0 ),
% 3.36/0.95      inference(equality_resolution_simp,[status(thm)],[c_6515]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_8709,plain,
% 3.36/0.95      ( k1_xboole_0 = X0 ),
% 3.36/0.95      inference(global_propositional_subsumption,
% 3.36/0.95                [status(thm)],
% 3.36/0.95                [c_6589,c_25,c_24,c_23,c_32,c_33,c_1025,c_1027,c_1029,c_6516]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_8782,plain,
% 3.36/0.95      ( k1_xboole_0 != k1_xboole_0 ),
% 3.36/0.95      inference(demodulation,[status(thm)],[c_8709,c_23]) ).
% 3.36/0.95  
% 3.36/0.95  cnf(c_8802,plain,
% 3.36/0.95      ( $false ),
% 3.36/0.95      inference(equality_resolution_simp,[status(thm)],[c_8782]) ).
% 3.36/0.95  
% 3.36/0.95  
% 3.36/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/0.95  
% 3.36/0.95  ------                               Statistics
% 3.36/0.95  
% 3.36/0.95  ------ General
% 3.36/0.95  
% 3.36/0.95  abstr_ref_over_cycles:                  0
% 3.36/0.95  abstr_ref_under_cycles:                 0
% 3.36/0.95  gc_basic_clause_elim:                   0
% 3.36/0.95  forced_gc_time:                         0
% 3.36/0.95  parsing_time:                           0.009
% 3.36/0.95  unif_index_cands_time:                  0.
% 3.36/0.95  unif_index_add_time:                    0.
% 3.36/0.95  orderings_time:                         0.
% 3.36/0.95  out_proof_time:                         0.008
% 3.36/0.95  total_time:                             0.243
% 3.36/0.95  num_of_symbols:                         52
% 3.36/0.95  num_of_terms:                           9906
% 3.36/0.95  
% 3.36/0.95  ------ Preprocessing
% 3.36/0.95  
% 3.36/0.95  num_of_splits:                          0
% 3.36/0.95  num_of_split_atoms:                     0
% 3.36/0.95  num_of_reused_defs:                     0
% 3.36/0.95  num_eq_ax_congr_red:                    45
% 3.36/0.95  num_of_sem_filtered_clauses:            1
% 3.36/0.95  num_of_subtypes:                        0
% 3.36/0.95  monotx_restored_types:                  0
% 3.36/0.95  sat_num_of_epr_types:                   0
% 3.36/0.95  sat_num_of_non_cyclic_types:            0
% 3.36/0.95  sat_guarded_non_collapsed_types:        0
% 3.36/0.95  num_pure_diseq_elim:                    0
% 3.36/0.95  simp_replaced_by:                       0
% 3.36/0.95  res_preprocessed:                       130
% 3.36/0.95  prep_upred:                             0
% 3.36/0.95  prep_unflattend:                        9
% 3.36/0.95  smt_new_axioms:                         0
% 3.36/0.95  pred_elim_cands:                        3
% 3.36/0.95  pred_elim:                              1
% 3.36/0.95  pred_elim_cl:                           1
% 3.36/0.95  pred_elim_cycles:                       3
% 3.36/0.95  merged_defs:                            0
% 3.36/0.95  merged_defs_ncl:                        0
% 3.36/0.95  bin_hyper_res:                          0
% 3.36/0.95  prep_cycles:                            4
% 3.36/0.95  pred_elim_time:                         0.003
% 3.36/0.95  splitting_time:                         0.
% 3.36/0.95  sem_filter_time:                        0.
% 3.36/0.95  monotx_time:                            0.
% 3.36/0.95  subtype_inf_time:                       0.
% 3.36/0.95  
% 3.36/0.95  ------ Problem properties
% 3.36/0.95  
% 3.36/0.95  clauses:                                27
% 3.36/0.95  conjectures:                            6
% 3.36/0.95  epr:                                    7
% 3.36/0.95  horn:                                   20
% 3.36/0.95  ground:                                 6
% 3.36/0.95  unary:                                  11
% 3.36/0.95  binary:                                 8
% 3.36/0.95  lits:                                   61
% 3.36/0.95  lits_eq:                                33
% 3.36/0.95  fd_pure:                                0
% 3.36/0.95  fd_pseudo:                              0
% 3.36/0.95  fd_cond:                                8
% 3.36/0.95  fd_pseudo_cond:                         0
% 3.36/0.95  ac_symbols:                             0
% 3.36/0.95  
% 3.36/0.95  ------ Propositional Solver
% 3.36/0.95  
% 3.36/0.95  prop_solver_calls:                      27
% 3.36/0.95  prop_fast_solver_calls:                 982
% 3.36/0.95  smt_solver_calls:                       0
% 3.36/0.95  smt_fast_solver_calls:                  0
% 3.36/0.95  prop_num_of_clauses:                    2480
% 3.36/0.95  prop_preprocess_simplified:             8067
% 3.36/0.95  prop_fo_subsumed:                       39
% 3.36/0.95  prop_solver_time:                       0.
% 3.36/0.95  smt_solver_time:                        0.
% 3.36/0.95  smt_fast_solver_time:                   0.
% 3.36/0.95  prop_fast_solver_time:                  0.
% 3.36/0.95  prop_unsat_core_time:                   0.
% 3.36/0.95  
% 3.36/0.95  ------ QBF
% 3.36/0.95  
% 3.36/0.95  qbf_q_res:                              0
% 3.36/0.95  qbf_num_tautologies:                    0
% 3.36/0.95  qbf_prep_cycles:                        0
% 3.36/0.95  
% 3.36/0.95  ------ BMC1
% 3.36/0.95  
% 3.36/0.95  bmc1_current_bound:                     -1
% 3.36/0.95  bmc1_last_solved_bound:                 -1
% 3.36/0.95  bmc1_unsat_core_size:                   -1
% 3.36/0.95  bmc1_unsat_core_parents_size:           -1
% 3.36/0.95  bmc1_merge_next_fun:                    0
% 3.36/0.95  bmc1_unsat_core_clauses_time:           0.
% 3.36/0.95  
% 3.36/0.95  ------ Instantiation
% 3.36/0.95  
% 3.36/0.95  inst_num_of_clauses:                    1020
% 3.36/0.95  inst_num_in_passive:                    108
% 3.36/0.95  inst_num_in_active:                     588
% 3.36/0.95  inst_num_in_unprocessed:                324
% 3.36/0.95  inst_num_of_loops:                      600
% 3.36/0.95  inst_num_of_learning_restarts:          0
% 3.36/0.95  inst_num_moves_active_passive:          11
% 3.36/0.95  inst_lit_activity:                      0
% 3.36/0.95  inst_lit_activity_moves:                0
% 3.36/0.95  inst_num_tautologies:                   0
% 3.36/0.95  inst_num_prop_implied:                  0
% 3.36/0.95  inst_num_existing_simplified:           0
% 3.36/0.95  inst_num_eq_res_simplified:             0
% 3.36/0.95  inst_num_child_elim:                    0
% 3.36/0.95  inst_num_of_dismatching_blockings:      46
% 3.36/0.95  inst_num_of_non_proper_insts:           596
% 3.36/0.95  inst_num_of_duplicates:                 0
% 3.36/0.95  inst_inst_num_from_inst_to_res:         0
% 3.36/0.95  inst_dismatching_checking_time:         0.
% 3.36/0.95  
% 3.36/0.95  ------ Resolution
% 3.36/0.95  
% 3.36/0.95  res_num_of_clauses:                     0
% 3.36/0.95  res_num_in_passive:                     0
% 3.36/0.95  res_num_in_active:                      0
% 3.36/0.95  res_num_of_loops:                       134
% 3.36/0.95  res_forward_subset_subsumed:            37
% 3.36/0.95  res_backward_subset_subsumed:           0
% 3.36/0.95  res_forward_subsumed:                   0
% 3.36/0.95  res_backward_subsumed:                  0
% 3.36/0.95  res_forward_subsumption_resolution:     0
% 3.36/0.95  res_backward_subsumption_resolution:    0
% 3.36/0.95  res_clause_to_clause_subsumption:       890
% 3.36/0.95  res_orphan_elimination:                 0
% 3.36/0.95  res_tautology_del:                      23
% 3.36/0.95  res_num_eq_res_simplified:              0
% 3.36/0.95  res_num_sel_changes:                    0
% 3.36/0.95  res_moves_from_active_to_pass:          0
% 3.36/0.95  
% 3.36/0.95  ------ Superposition
% 3.36/0.95  
% 3.36/0.95  sup_time_total:                         0.
% 3.36/0.95  sup_time_generating:                    0.
% 3.36/0.95  sup_time_sim_full:                      0.
% 3.36/0.95  sup_time_sim_immed:                     0.
% 3.36/0.95  
% 3.36/0.95  sup_num_of_clauses:                     138
% 3.36/0.95  sup_num_in_active:                      7
% 3.36/0.95  sup_num_in_passive:                     131
% 3.36/0.95  sup_num_of_loops:                       119
% 3.36/0.95  sup_fw_superposition:                   361
% 3.36/0.95  sup_bw_superposition:                   966
% 3.36/0.95  sup_immediate_simplified:               596
% 3.36/0.95  sup_given_eliminated:                   0
% 3.36/0.95  comparisons_done:                       0
% 3.36/0.95  comparisons_avoided:                    42
% 3.36/0.95  
% 3.36/0.95  ------ Simplifications
% 3.36/0.95  
% 3.36/0.95  
% 3.36/0.95  sim_fw_subset_subsumed:                 376
% 3.36/0.95  sim_bw_subset_subsumed:                 30
% 3.36/0.95  sim_fw_subsumed:                        115
% 3.36/0.95  sim_bw_subsumed:                        39
% 3.36/0.95  sim_fw_subsumption_res:                 0
% 3.36/0.95  sim_bw_subsumption_res:                 0
% 3.36/0.95  sim_tautology_del:                      14
% 3.36/0.95  sim_eq_tautology_del:                   65
% 3.36/0.95  sim_eq_res_simp:                        15
% 3.36/0.95  sim_fw_demodulated:                     43
% 3.36/0.95  sim_bw_demodulated:                     102
% 3.36/0.95  sim_light_normalised:                   64
% 3.36/0.95  sim_joinable_taut:                      0
% 3.36/0.95  sim_joinable_simp:                      0
% 3.36/0.95  sim_ac_normalised:                      0
% 3.36/0.95  sim_smt_subsumption:                    0
% 3.36/0.95  
%------------------------------------------------------------------------------
