%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:53 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :  188 (1706 expanded)
%              Number of clauses        :  111 ( 509 expanded)
%              Number of leaves         :   22 ( 385 expanded)
%              Depth                    :   25
%              Number of atoms          :  527 (7322 expanded)
%              Number of equality atoms :  300 (3633 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f34,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f34])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X5
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X5
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f42])).

fof(f68,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f68,f56])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f40])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f70,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f70,f45])).

fof(f71,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    o_0_0_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f71,f45])).

fof(f72,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    o_0_0_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f72,f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f38])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X5
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X5
      | k4_tarski(k4_tarski(X5,X6),X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f69,f55])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f56,f45,f45,f45])).

fof(f73,plain,(
    k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f56,f45,f45,f45])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_861,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_873,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2627,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_873])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_zfmisc_1(X2,X3) != X1
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_275,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_860,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_2678,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_860])).

cnf(c_17,plain,
    ( r2_hidden(sK1(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_866,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_878,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1312,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_878])).

cnf(c_2938,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = o_0_0_xboole_0
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_2678,c_1312])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_871,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3806,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | m1_subset_1(X0,o_0_0_xboole_0) != iProver_top
    | m1_subset_1(k7_mcart_1(sK2,sK3,sK4,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_871])).

cnf(c_24,negated_conjecture,
    ( o_0_0_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_23,negated_conjecture,
    ( o_0_0_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,negated_conjecture,
    ( o_0_0_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1045,plain,
    ( r2_hidden(sK1(sK4),sK4)
    | o_0_0_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1048,plain,
    ( r2_hidden(sK1(sK3),sK3)
    | o_0_0_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1051,plain,
    ( r2_hidden(sK1(sK2),sK2)
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X1,X0),X1) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_1140,plain,
    ( r2_hidden(sK0(sK4,sK1(sK4)),sK4)
    | ~ r2_hidden(sK1(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_2698,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2678])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1159,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK1(sK3)),k2_zfmisc_1(X1,sK3))
    | ~ r2_hidden(sK1(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3303,plain,
    ( r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(sK1(sK3),sK3)
    | ~ r2_hidden(sK1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_1456,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK0(sK4,sK1(sK4))),k2_zfmisc_1(X1,sK4))
    | ~ r2_hidden(sK0(sK4,sK1(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5023,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(sK0(sK4,sK1(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_2190,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_36414,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_36477,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3806,c_24,c_23,c_22,c_1045,c_1048,c_1051,c_1140,c_2698,c_3303,c_5023,c_36414])).

cnf(c_877,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_870,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3009,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k2_mcart_1(k4_tarski(X2,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_870])).

cnf(c_17977,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_3009])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_874,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_18664,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17977,c_874])).

cnf(c_1046,plain,
    ( o_0_0_xboole_0 = sK4
    | r2_hidden(sK1(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_1049,plain,
    ( o_0_0_xboole_0 = sK3
    | r2_hidden(sK1(sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1048])).

cnf(c_1052,plain,
    ( o_0_0_xboole_0 = sK2
    | r2_hidden(sK1(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_1152,plain,
    ( r2_hidden(sK0(sK4,sK1(sK4)),sK4) = iProver_top
    | r2_hidden(sK1(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_3304,plain,
    ( r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r2_hidden(sK1(sK3),sK3) != iProver_top
    | r2_hidden(sK1(sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3303])).

cnf(c_5050,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3)) != iProver_top
    | r2_hidden(sK0(sK4,sK1(sK4)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5023])).

cnf(c_36415,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36414])).

cnf(c_40233,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18664,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,c_3304,c_5050,c_36415])).

cnf(c_40234,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_40233])).

cnf(c_40239,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_40234,c_873])).

cnf(c_43059,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40239,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,c_3304,c_5050,c_17977,c_36415])).

cnf(c_43060,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_43059])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_869,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_43074,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(k2_mcart_1(k4_tarski(sK6,X0))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_43060,c_869])).

cnf(c_45478,plain,
    ( r2_hidden(k1_mcart_1(k2_mcart_1(k4_tarski(sK6,sK6))),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_43074])).

cnf(c_46609,plain,
    ( r2_hidden(k1_mcart_1(k2_mcart_1(k4_tarski(sK6,sK6))),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45478,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,c_3304,c_5050,c_36415])).

cnf(c_2677,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_869])).

cnf(c_3352,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_860])).

cnf(c_3004,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_878])).

cnf(c_10830,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3352,c_3004])).

cnf(c_46630,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_46609,c_10830])).

cnf(c_3382,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3352])).

cnf(c_48575,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46630,c_24,c_23,c_22,c_1045,c_1048,c_1051,c_1140,c_3303,c_3382,c_5023,c_36414])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ m1_subset_1(X1,sK3)
    | ~ m1_subset_1(X2,sK2)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK6
    | sK5 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_862,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
    | sK5 = X0
    | m1_subset_1(X2,sK4) != iProver_top
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_48582,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | k1_mcart_1(k1_mcart_1(sK6)) = sK5
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_48575,c_862])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_863,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2278,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_861,c_863])).

cnf(c_496,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_513,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_497,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1061,plain,
    ( sK4 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1062,plain,
    ( sK4 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_1063,plain,
    ( sK3 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1064,plain,
    ( sK3 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_1065,plain,
    ( sK2 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1066,plain,
    ( sK2 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_2699,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2278,c_24,c_23,c_22,c_513,c_1062,c_1064,c_1066])).

cnf(c_21,negated_conjecture,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2702,plain,
    ( k1_mcart_1(k1_mcart_1(sK6)) != sK5 ),
    inference(demodulation,[status(thm)],[c_2699,c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_872,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2969,plain,
    ( m1_subset_1(k5_mcart_1(sK2,sK3,sK4,sK6),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_872])).

cnf(c_2976,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2969,c_2699])).

cnf(c_3350,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_870])).

cnf(c_10832,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_3004])).

cnf(c_46631,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_46609,c_10832])).

cnf(c_48279,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46631,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,c_3304,c_3350,c_5050,c_36415])).

cnf(c_48287,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_48279,c_874])).

cnf(c_48619,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48582,c_2702,c_2976,c_48287])).

cnf(c_48627,plain,
    ( m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_36477,c_48619])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_865,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3056,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | sK4 = o_0_0_xboole_0
    | sK3 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_861,c_865])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,X1),X2))
    | k7_mcart_1(sK2,X1,X2,X0) = k2_mcart_1(X0)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X1))
    | k7_mcart_1(sK2,sK3,X1,X0) = k2_mcart_1(X0)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1683,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k7_mcart_1(sK2,sK3,sK4,X0) = k2_mcart_1(X0)
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_2657,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | o_0_0_xboole_0 = sK4
    | o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_3143,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3056,c_26,c_24,c_23,c_22,c_2657])).

cnf(c_2645,plain,
    ( m1_subset_1(k7_mcart_1(sK2,sK3,sK4,sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_871])).

cnf(c_3147,plain,
    ( m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3143,c_2645])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48627,c_3147])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:48:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 11.48/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.48/1.98  
% 11.48/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.48/1.98  
% 11.48/1.98  ------  iProver source info
% 11.48/1.98  
% 11.48/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.48/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.48/1.98  git: non_committed_changes: false
% 11.48/1.98  git: last_make_outside_of_git: false
% 11.48/1.98  
% 11.48/1.98  ------ 
% 11.48/1.98  
% 11.48/1.98  ------ Input Options
% 11.48/1.98  
% 11.48/1.98  --out_options                           all
% 11.48/1.98  --tptp_safe_out                         true
% 11.48/1.98  --problem_path                          ""
% 11.48/1.98  --include_path                          ""
% 11.48/1.98  --clausifier                            res/vclausify_rel
% 11.48/1.98  --clausifier_options                    --mode clausify
% 11.48/1.98  --stdin                                 false
% 11.48/1.98  --stats_out                             all
% 11.48/1.98  
% 11.48/1.98  ------ General Options
% 11.48/1.98  
% 11.48/1.98  --fof                                   false
% 11.48/1.98  --time_out_real                         305.
% 11.48/1.98  --time_out_virtual                      -1.
% 11.48/1.98  --symbol_type_check                     false
% 11.48/1.98  --clausify_out                          false
% 11.48/1.98  --sig_cnt_out                           false
% 11.48/1.98  --trig_cnt_out                          false
% 11.48/1.98  --trig_cnt_out_tolerance                1.
% 11.48/1.98  --trig_cnt_out_sk_spl                   false
% 11.48/1.98  --abstr_cl_out                          false
% 11.48/1.98  
% 11.48/1.98  ------ Global Options
% 11.48/1.98  
% 11.48/1.98  --schedule                              default
% 11.48/1.98  --add_important_lit                     false
% 11.48/1.98  --prop_solver_per_cl                    1000
% 11.48/1.98  --min_unsat_core                        false
% 11.48/1.98  --soft_assumptions                      false
% 11.48/1.98  --soft_lemma_size                       3
% 11.48/1.98  --prop_impl_unit_size                   0
% 11.48/1.98  --prop_impl_unit                        []
% 11.48/1.98  --share_sel_clauses                     true
% 11.48/1.98  --reset_solvers                         false
% 11.48/1.98  --bc_imp_inh                            [conj_cone]
% 11.48/1.98  --conj_cone_tolerance                   3.
% 11.48/1.98  --extra_neg_conj                        none
% 11.48/1.98  --large_theory_mode                     true
% 11.48/1.98  --prolific_symb_bound                   200
% 11.48/1.98  --lt_threshold                          2000
% 11.48/1.98  --clause_weak_htbl                      true
% 11.48/1.98  --gc_record_bc_elim                     false
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing Options
% 11.48/1.98  
% 11.48/1.98  --preprocessing_flag                    true
% 11.48/1.98  --time_out_prep_mult                    0.1
% 11.48/1.98  --splitting_mode                        input
% 11.48/1.98  --splitting_grd                         true
% 11.48/1.98  --splitting_cvd                         false
% 11.48/1.98  --splitting_cvd_svl                     false
% 11.48/1.98  --splitting_nvd                         32
% 11.48/1.98  --sub_typing                            true
% 11.48/1.98  --prep_gs_sim                           true
% 11.48/1.98  --prep_unflatten                        true
% 11.48/1.98  --prep_res_sim                          true
% 11.48/1.98  --prep_upred                            true
% 11.48/1.98  --prep_sem_filter                       exhaustive
% 11.48/1.98  --prep_sem_filter_out                   false
% 11.48/1.98  --pred_elim                             true
% 11.48/1.98  --res_sim_input                         true
% 11.48/1.98  --eq_ax_congr_red                       true
% 11.48/1.98  --pure_diseq_elim                       true
% 11.48/1.98  --brand_transform                       false
% 11.48/1.98  --non_eq_to_eq                          false
% 11.48/1.98  --prep_def_merge                        true
% 11.48/1.98  --prep_def_merge_prop_impl              false
% 11.48/1.98  --prep_def_merge_mbd                    true
% 11.48/1.98  --prep_def_merge_tr_red                 false
% 11.48/1.98  --prep_def_merge_tr_cl                  false
% 11.48/1.98  --smt_preprocessing                     true
% 11.48/1.98  --smt_ac_axioms                         fast
% 11.48/1.98  --preprocessed_out                      false
% 11.48/1.98  --preprocessed_stats                    false
% 11.48/1.98  
% 11.48/1.98  ------ Abstraction refinement Options
% 11.48/1.98  
% 11.48/1.98  --abstr_ref                             []
% 11.48/1.98  --abstr_ref_prep                        false
% 11.48/1.98  --abstr_ref_until_sat                   false
% 11.48/1.98  --abstr_ref_sig_restrict                funpre
% 11.48/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.48/1.98  --abstr_ref_under                       []
% 11.48/1.98  
% 11.48/1.98  ------ SAT Options
% 11.48/1.98  
% 11.48/1.98  --sat_mode                              false
% 11.48/1.98  --sat_fm_restart_options                ""
% 11.48/1.98  --sat_gr_def                            false
% 11.48/1.98  --sat_epr_types                         true
% 11.48/1.98  --sat_non_cyclic_types                  false
% 11.48/1.98  --sat_finite_models                     false
% 11.48/1.98  --sat_fm_lemmas                         false
% 11.48/1.98  --sat_fm_prep                           false
% 11.48/1.98  --sat_fm_uc_incr                        true
% 11.48/1.98  --sat_out_model                         small
% 11.48/1.98  --sat_out_clauses                       false
% 11.48/1.98  
% 11.48/1.98  ------ QBF Options
% 11.48/1.98  
% 11.48/1.98  --qbf_mode                              false
% 11.48/1.98  --qbf_elim_univ                         false
% 11.48/1.98  --qbf_dom_inst                          none
% 11.48/1.98  --qbf_dom_pre_inst                      false
% 11.48/1.98  --qbf_sk_in                             false
% 11.48/1.98  --qbf_pred_elim                         true
% 11.48/1.98  --qbf_split                             512
% 11.48/1.98  
% 11.48/1.98  ------ BMC1 Options
% 11.48/1.98  
% 11.48/1.98  --bmc1_incremental                      false
% 11.48/1.98  --bmc1_axioms                           reachable_all
% 11.48/1.98  --bmc1_min_bound                        0
% 11.48/1.98  --bmc1_max_bound                        -1
% 11.48/1.98  --bmc1_max_bound_default                -1
% 11.48/1.98  --bmc1_symbol_reachability              true
% 11.48/1.98  --bmc1_property_lemmas                  false
% 11.48/1.98  --bmc1_k_induction                      false
% 11.48/1.98  --bmc1_non_equiv_states                 false
% 11.48/1.98  --bmc1_deadlock                         false
% 11.48/1.98  --bmc1_ucm                              false
% 11.48/1.98  --bmc1_add_unsat_core                   none
% 11.48/1.98  --bmc1_unsat_core_children              false
% 11.48/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.48/1.98  --bmc1_out_stat                         full
% 11.48/1.98  --bmc1_ground_init                      false
% 11.48/1.98  --bmc1_pre_inst_next_state              false
% 11.48/1.98  --bmc1_pre_inst_state                   false
% 11.48/1.98  --bmc1_pre_inst_reach_state             false
% 11.48/1.98  --bmc1_out_unsat_core                   false
% 11.48/1.98  --bmc1_aig_witness_out                  false
% 11.48/1.98  --bmc1_verbose                          false
% 11.48/1.98  --bmc1_dump_clauses_tptp                false
% 11.48/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.48/1.98  --bmc1_dump_file                        -
% 11.48/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.48/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.48/1.98  --bmc1_ucm_extend_mode                  1
% 11.48/1.98  --bmc1_ucm_init_mode                    2
% 11.48/1.98  --bmc1_ucm_cone_mode                    none
% 11.48/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.48/1.98  --bmc1_ucm_relax_model                  4
% 11.48/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.48/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.48/1.98  --bmc1_ucm_layered_model                none
% 11.48/1.98  --bmc1_ucm_max_lemma_size               10
% 11.48/1.98  
% 11.48/1.98  ------ AIG Options
% 11.48/1.98  
% 11.48/1.98  --aig_mode                              false
% 11.48/1.98  
% 11.48/1.98  ------ Instantiation Options
% 11.48/1.98  
% 11.48/1.98  --instantiation_flag                    true
% 11.48/1.98  --inst_sos_flag                         false
% 11.48/1.98  --inst_sos_phase                        true
% 11.48/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.48/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.48/1.98  --inst_lit_sel_side                     num_symb
% 11.48/1.98  --inst_solver_per_active                1400
% 11.48/1.98  --inst_solver_calls_frac                1.
% 11.48/1.98  --inst_passive_queue_type               priority_queues
% 11.48/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.48/1.98  --inst_passive_queues_freq              [25;2]
% 11.48/1.98  --inst_dismatching                      true
% 11.48/1.98  --inst_eager_unprocessed_to_passive     true
% 11.48/1.98  --inst_prop_sim_given                   true
% 11.48/1.98  --inst_prop_sim_new                     false
% 11.48/1.98  --inst_subs_new                         false
% 11.48/1.98  --inst_eq_res_simp                      false
% 11.48/1.98  --inst_subs_given                       false
% 11.48/1.98  --inst_orphan_elimination               true
% 11.48/1.98  --inst_learning_loop_flag               true
% 11.48/1.98  --inst_learning_start                   3000
% 11.48/1.98  --inst_learning_factor                  2
% 11.48/1.98  --inst_start_prop_sim_after_learn       3
% 11.48/1.98  --inst_sel_renew                        solver
% 11.48/1.98  --inst_lit_activity_flag                true
% 11.48/1.98  --inst_restr_to_given                   false
% 11.48/1.98  --inst_activity_threshold               500
% 11.48/1.98  --inst_out_proof                        true
% 11.48/1.98  
% 11.48/1.98  ------ Resolution Options
% 11.48/1.98  
% 11.48/1.98  --resolution_flag                       true
% 11.48/1.98  --res_lit_sel                           adaptive
% 11.48/1.98  --res_lit_sel_side                      none
% 11.48/1.98  --res_ordering                          kbo
% 11.48/1.98  --res_to_prop_solver                    active
% 11.48/1.98  --res_prop_simpl_new                    false
% 11.48/1.98  --res_prop_simpl_given                  true
% 11.48/1.98  --res_passive_queue_type                priority_queues
% 11.48/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.48/1.98  --res_passive_queues_freq               [15;5]
% 11.48/1.98  --res_forward_subs                      full
% 11.48/1.98  --res_backward_subs                     full
% 11.48/1.98  --res_forward_subs_resolution           true
% 11.48/1.98  --res_backward_subs_resolution          true
% 11.48/1.98  --res_orphan_elimination                true
% 11.48/1.98  --res_time_limit                        2.
% 11.48/1.98  --res_out_proof                         true
% 11.48/1.98  
% 11.48/1.98  ------ Superposition Options
% 11.48/1.98  
% 11.48/1.98  --superposition_flag                    true
% 11.48/1.98  --sup_passive_queue_type                priority_queues
% 11.48/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.48/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.48/1.98  --demod_completeness_check              fast
% 11.48/1.98  --demod_use_ground                      true
% 11.48/1.98  --sup_to_prop_solver                    passive
% 11.48/1.98  --sup_prop_simpl_new                    true
% 11.48/1.98  --sup_prop_simpl_given                  true
% 11.48/1.98  --sup_fun_splitting                     false
% 11.48/1.98  --sup_smt_interval                      50000
% 11.48/1.98  
% 11.48/1.98  ------ Superposition Simplification Setup
% 11.48/1.98  
% 11.48/1.98  --sup_indices_passive                   []
% 11.48/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.48/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_full_bw                           [BwDemod]
% 11.48/1.98  --sup_immed_triv                        [TrivRules]
% 11.48/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_immed_bw_main                     []
% 11.48/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.48/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.98  
% 11.48/1.98  ------ Combination Options
% 11.48/1.98  
% 11.48/1.98  --comb_res_mult                         3
% 11.48/1.98  --comb_sup_mult                         2
% 11.48/1.98  --comb_inst_mult                        10
% 11.48/1.98  
% 11.48/1.98  ------ Debug Options
% 11.48/1.98  
% 11.48/1.98  --dbg_backtrace                         false
% 11.48/1.98  --dbg_dump_prop_clauses                 false
% 11.48/1.98  --dbg_dump_prop_clauses_file            -
% 11.48/1.98  --dbg_out_stat                          false
% 11.48/1.98  ------ Parsing...
% 11.48/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.48/1.98  ------ Proving...
% 11.48/1.98  ------ Problem Properties 
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  clauses                                 25
% 11.48/1.98  conjectures                             6
% 11.48/1.98  EPR                                     6
% 11.48/1.98  Horn                                    20
% 11.48/1.98  unary                                   5
% 11.48/1.98  binary                                  12
% 11.48/1.98  lits                                    61
% 11.48/1.98  lits eq                                 24
% 11.48/1.98  fd_pure                                 0
% 11.48/1.98  fd_pseudo                               0
% 11.48/1.98  fd_cond                                 7
% 11.48/1.98  fd_pseudo_cond                          0
% 11.48/1.98  AC symbols                              0
% 11.48/1.98  
% 11.48/1.98  ------ Schedule dynamic 5 is on 
% 11.48/1.98  
% 11.48/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  ------ 
% 11.48/1.98  Current options:
% 11.48/1.98  ------ 
% 11.48/1.98  
% 11.48/1.98  ------ Input Options
% 11.48/1.98  
% 11.48/1.98  --out_options                           all
% 11.48/1.98  --tptp_safe_out                         true
% 11.48/1.98  --problem_path                          ""
% 11.48/1.98  --include_path                          ""
% 11.48/1.98  --clausifier                            res/vclausify_rel
% 11.48/1.98  --clausifier_options                    --mode clausify
% 11.48/1.98  --stdin                                 false
% 11.48/1.98  --stats_out                             all
% 11.48/1.98  
% 11.48/1.98  ------ General Options
% 11.48/1.98  
% 11.48/1.98  --fof                                   false
% 11.48/1.98  --time_out_real                         305.
% 11.48/1.98  --time_out_virtual                      -1.
% 11.48/1.98  --symbol_type_check                     false
% 11.48/1.98  --clausify_out                          false
% 11.48/1.98  --sig_cnt_out                           false
% 11.48/1.98  --trig_cnt_out                          false
% 11.48/1.98  --trig_cnt_out_tolerance                1.
% 11.48/1.98  --trig_cnt_out_sk_spl                   false
% 11.48/1.98  --abstr_cl_out                          false
% 11.48/1.98  
% 11.48/1.98  ------ Global Options
% 11.48/1.98  
% 11.48/1.98  --schedule                              default
% 11.48/1.98  --add_important_lit                     false
% 11.48/1.98  --prop_solver_per_cl                    1000
% 11.48/1.98  --min_unsat_core                        false
% 11.48/1.98  --soft_assumptions                      false
% 11.48/1.98  --soft_lemma_size                       3
% 11.48/1.98  --prop_impl_unit_size                   0
% 11.48/1.98  --prop_impl_unit                        []
% 11.48/1.98  --share_sel_clauses                     true
% 11.48/1.98  --reset_solvers                         false
% 11.48/1.98  --bc_imp_inh                            [conj_cone]
% 11.48/1.98  --conj_cone_tolerance                   3.
% 11.48/1.98  --extra_neg_conj                        none
% 11.48/1.98  --large_theory_mode                     true
% 11.48/1.98  --prolific_symb_bound                   200
% 11.48/1.98  --lt_threshold                          2000
% 11.48/1.98  --clause_weak_htbl                      true
% 11.48/1.98  --gc_record_bc_elim                     false
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing Options
% 11.48/1.98  
% 11.48/1.98  --preprocessing_flag                    true
% 11.48/1.98  --time_out_prep_mult                    0.1
% 11.48/1.98  --splitting_mode                        input
% 11.48/1.98  --splitting_grd                         true
% 11.48/1.98  --splitting_cvd                         false
% 11.48/1.98  --splitting_cvd_svl                     false
% 11.48/1.98  --splitting_nvd                         32
% 11.48/1.98  --sub_typing                            true
% 11.48/1.98  --prep_gs_sim                           true
% 11.48/1.98  --prep_unflatten                        true
% 11.48/1.98  --prep_res_sim                          true
% 11.48/1.98  --prep_upred                            true
% 11.48/1.98  --prep_sem_filter                       exhaustive
% 11.48/1.98  --prep_sem_filter_out                   false
% 11.48/1.98  --pred_elim                             true
% 11.48/1.98  --res_sim_input                         true
% 11.48/1.98  --eq_ax_congr_red                       true
% 11.48/1.98  --pure_diseq_elim                       true
% 11.48/1.98  --brand_transform                       false
% 11.48/1.98  --non_eq_to_eq                          false
% 11.48/1.98  --prep_def_merge                        true
% 11.48/1.98  --prep_def_merge_prop_impl              false
% 11.48/1.98  --prep_def_merge_mbd                    true
% 11.48/1.98  --prep_def_merge_tr_red                 false
% 11.48/1.98  --prep_def_merge_tr_cl                  false
% 11.48/1.98  --smt_preprocessing                     true
% 11.48/1.98  --smt_ac_axioms                         fast
% 11.48/1.98  --preprocessed_out                      false
% 11.48/1.98  --preprocessed_stats                    false
% 11.48/1.98  
% 11.48/1.98  ------ Abstraction refinement Options
% 11.48/1.98  
% 11.48/1.98  --abstr_ref                             []
% 11.48/1.98  --abstr_ref_prep                        false
% 11.48/1.98  --abstr_ref_until_sat                   false
% 11.48/1.98  --abstr_ref_sig_restrict                funpre
% 11.48/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.48/1.98  --abstr_ref_under                       []
% 11.48/1.98  
% 11.48/1.98  ------ SAT Options
% 11.48/1.98  
% 11.48/1.98  --sat_mode                              false
% 11.48/1.98  --sat_fm_restart_options                ""
% 11.48/1.98  --sat_gr_def                            false
% 11.48/1.98  --sat_epr_types                         true
% 11.48/1.98  --sat_non_cyclic_types                  false
% 11.48/1.98  --sat_finite_models                     false
% 11.48/1.98  --sat_fm_lemmas                         false
% 11.48/1.98  --sat_fm_prep                           false
% 11.48/1.98  --sat_fm_uc_incr                        true
% 11.48/1.98  --sat_out_model                         small
% 11.48/1.98  --sat_out_clauses                       false
% 11.48/1.98  
% 11.48/1.98  ------ QBF Options
% 11.48/1.98  
% 11.48/1.98  --qbf_mode                              false
% 11.48/1.98  --qbf_elim_univ                         false
% 11.48/1.98  --qbf_dom_inst                          none
% 11.48/1.98  --qbf_dom_pre_inst                      false
% 11.48/1.98  --qbf_sk_in                             false
% 11.48/1.98  --qbf_pred_elim                         true
% 11.48/1.98  --qbf_split                             512
% 11.48/1.98  
% 11.48/1.98  ------ BMC1 Options
% 11.48/1.98  
% 11.48/1.98  --bmc1_incremental                      false
% 11.48/1.98  --bmc1_axioms                           reachable_all
% 11.48/1.98  --bmc1_min_bound                        0
% 11.48/1.98  --bmc1_max_bound                        -1
% 11.48/1.98  --bmc1_max_bound_default                -1
% 11.48/1.98  --bmc1_symbol_reachability              true
% 11.48/1.98  --bmc1_property_lemmas                  false
% 11.48/1.98  --bmc1_k_induction                      false
% 11.48/1.98  --bmc1_non_equiv_states                 false
% 11.48/1.98  --bmc1_deadlock                         false
% 11.48/1.98  --bmc1_ucm                              false
% 11.48/1.98  --bmc1_add_unsat_core                   none
% 11.48/1.98  --bmc1_unsat_core_children              false
% 11.48/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.48/1.98  --bmc1_out_stat                         full
% 11.48/1.98  --bmc1_ground_init                      false
% 11.48/1.98  --bmc1_pre_inst_next_state              false
% 11.48/1.98  --bmc1_pre_inst_state                   false
% 11.48/1.98  --bmc1_pre_inst_reach_state             false
% 11.48/1.98  --bmc1_out_unsat_core                   false
% 11.48/1.98  --bmc1_aig_witness_out                  false
% 11.48/1.98  --bmc1_verbose                          false
% 11.48/1.98  --bmc1_dump_clauses_tptp                false
% 11.48/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.48/1.98  --bmc1_dump_file                        -
% 11.48/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.48/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.48/1.98  --bmc1_ucm_extend_mode                  1
% 11.48/1.98  --bmc1_ucm_init_mode                    2
% 11.48/1.98  --bmc1_ucm_cone_mode                    none
% 11.48/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.48/1.98  --bmc1_ucm_relax_model                  4
% 11.48/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.48/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.48/1.98  --bmc1_ucm_layered_model                none
% 11.48/1.98  --bmc1_ucm_max_lemma_size               10
% 11.48/1.98  
% 11.48/1.98  ------ AIG Options
% 11.48/1.98  
% 11.48/1.98  --aig_mode                              false
% 11.48/1.98  
% 11.48/1.98  ------ Instantiation Options
% 11.48/1.98  
% 11.48/1.98  --instantiation_flag                    true
% 11.48/1.98  --inst_sos_flag                         false
% 11.48/1.98  --inst_sos_phase                        true
% 11.48/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.48/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.48/1.98  --inst_lit_sel_side                     none
% 11.48/1.98  --inst_solver_per_active                1400
% 11.48/1.98  --inst_solver_calls_frac                1.
% 11.48/1.98  --inst_passive_queue_type               priority_queues
% 11.48/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.48/1.98  --inst_passive_queues_freq              [25;2]
% 11.48/1.98  --inst_dismatching                      true
% 11.48/1.98  --inst_eager_unprocessed_to_passive     true
% 11.48/1.98  --inst_prop_sim_given                   true
% 11.48/1.98  --inst_prop_sim_new                     false
% 11.48/1.98  --inst_subs_new                         false
% 11.48/1.98  --inst_eq_res_simp                      false
% 11.48/1.98  --inst_subs_given                       false
% 11.48/1.98  --inst_orphan_elimination               true
% 11.48/1.98  --inst_learning_loop_flag               true
% 11.48/1.98  --inst_learning_start                   3000
% 11.48/1.98  --inst_learning_factor                  2
% 11.48/1.98  --inst_start_prop_sim_after_learn       3
% 11.48/1.98  --inst_sel_renew                        solver
% 11.48/1.98  --inst_lit_activity_flag                true
% 11.48/1.98  --inst_restr_to_given                   false
% 11.48/1.98  --inst_activity_threshold               500
% 11.48/1.98  --inst_out_proof                        true
% 11.48/1.98  
% 11.48/1.98  ------ Resolution Options
% 11.48/1.98  
% 11.48/1.98  --resolution_flag                       false
% 11.48/1.98  --res_lit_sel                           adaptive
% 11.48/1.98  --res_lit_sel_side                      none
% 11.48/1.98  --res_ordering                          kbo
% 11.48/1.98  --res_to_prop_solver                    active
% 11.48/1.98  --res_prop_simpl_new                    false
% 11.48/1.98  --res_prop_simpl_given                  true
% 11.48/1.98  --res_passive_queue_type                priority_queues
% 11.48/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.48/1.98  --res_passive_queues_freq               [15;5]
% 11.48/1.98  --res_forward_subs                      full
% 11.48/1.98  --res_backward_subs                     full
% 11.48/1.98  --res_forward_subs_resolution           true
% 11.48/1.98  --res_backward_subs_resolution          true
% 11.48/1.98  --res_orphan_elimination                true
% 11.48/1.98  --res_time_limit                        2.
% 11.48/1.98  --res_out_proof                         true
% 11.48/1.98  
% 11.48/1.98  ------ Superposition Options
% 11.48/1.98  
% 11.48/1.98  --superposition_flag                    true
% 11.48/1.98  --sup_passive_queue_type                priority_queues
% 11.48/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.48/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.48/1.98  --demod_completeness_check              fast
% 11.48/1.98  --demod_use_ground                      true
% 11.48/1.98  --sup_to_prop_solver                    passive
% 11.48/1.98  --sup_prop_simpl_new                    true
% 11.48/1.98  --sup_prop_simpl_given                  true
% 11.48/1.98  --sup_fun_splitting                     false
% 11.48/1.98  --sup_smt_interval                      50000
% 11.48/1.98  
% 11.48/1.98  ------ Superposition Simplification Setup
% 11.48/1.98  
% 11.48/1.98  --sup_indices_passive                   []
% 11.48/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.48/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_full_bw                           [BwDemod]
% 11.48/1.98  --sup_immed_triv                        [TrivRules]
% 11.48/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_immed_bw_main                     []
% 11.48/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.48/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.98  
% 11.48/1.98  ------ Combination Options
% 11.48/1.98  
% 11.48/1.98  --comb_res_mult                         3
% 11.48/1.98  --comb_sup_mult                         2
% 11.48/1.98  --comb_inst_mult                        10
% 11.48/1.98  
% 11.48/1.98  ------ Debug Options
% 11.48/1.98  
% 11.48/1.98  --dbg_backtrace                         false
% 11.48/1.98  --dbg_dump_prop_clauses                 false
% 11.48/1.98  --dbg_dump_prop_clauses_file            -
% 11.48/1.98  --dbg_out_stat                          false
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  ------ Proving...
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  % SZS status Theorem for theBenchmark.p
% 11.48/1.98  
% 11.48/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.48/1.98  
% 11.48/1.98  fof(f17,conjecture,(
% 11.48/1.98    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f18,negated_conjecture,(
% 11.48/1.98    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 11.48/1.98    inference(negated_conjecture,[],[f17])).
% 11.48/1.98  
% 11.48/1.98  fof(f34,plain,(
% 11.48/1.98    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 11.48/1.98    inference(ennf_transformation,[],[f18])).
% 11.48/1.98  
% 11.48/1.98  fof(f35,plain,(
% 11.48/1.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 11.48/1.98    inference(flattening,[],[f34])).
% 11.48/1.98  
% 11.48/1.98  fof(f42,plain,(
% 11.48/1.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X5 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 11.48/1.98    introduced(choice_axiom,[])).
% 11.48/1.98  
% 11.48/1.98  fof(f43,plain,(
% 11.48/1.98    k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X5 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 11.48/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f42])).
% 11.48/1.98  
% 11.48/1.98  fof(f68,plain,(
% 11.48/1.98    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 11.48/1.98    inference(cnf_transformation,[],[f43])).
% 11.48/1.98  
% 11.48/1.98  fof(f10,axiom,(
% 11.48/1.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f56,plain,(
% 11.48/1.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f10])).
% 11.48/1.98  
% 11.48/1.98  fof(f86,plain,(
% 11.48/1.98    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 11.48/1.98    inference(definition_unfolding,[],[f68,f56])).
% 11.48/1.98  
% 11.48/1.98  fof(f6,axiom,(
% 11.48/1.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f24,plain,(
% 11.48/1.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.48/1.98    inference(ennf_transformation,[],[f6])).
% 11.48/1.98  
% 11.48/1.98  fof(f25,plain,(
% 11.48/1.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.48/1.98    inference(flattening,[],[f24])).
% 11.48/1.98  
% 11.48/1.98  fof(f52,plain,(
% 11.48/1.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f25])).
% 11.48/1.98  
% 11.48/1.98  fof(f7,axiom,(
% 11.48/1.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f53,plain,(
% 11.48/1.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.48/1.98    inference(cnf_transformation,[],[f7])).
% 11.48/1.98  
% 11.48/1.98  fof(f14,axiom,(
% 11.48/1.98    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f30,plain,(
% 11.48/1.98    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 11.48/1.98    inference(ennf_transformation,[],[f14])).
% 11.48/1.98  
% 11.48/1.98  fof(f31,plain,(
% 11.48/1.98    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 11.48/1.98    inference(flattening,[],[f30])).
% 11.48/1.98  
% 11.48/1.98  fof(f61,plain,(
% 11.48/1.98    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f31])).
% 11.48/1.98  
% 11.48/1.98  fof(f15,axiom,(
% 11.48/1.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f32,plain,(
% 11.48/1.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 11.48/1.98    inference(ennf_transformation,[],[f15])).
% 11.48/1.98  
% 11.48/1.98  fof(f40,plain,(
% 11.48/1.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 11.48/1.98    introduced(choice_axiom,[])).
% 11.48/1.98  
% 11.48/1.98  fof(f41,plain,(
% 11.48/1.98    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 11.48/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f40])).
% 11.48/1.98  
% 11.48/1.98  fof(f62,plain,(
% 11.48/1.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 11.48/1.98    inference(cnf_transformation,[],[f41])).
% 11.48/1.98  
% 11.48/1.98  fof(f2,axiom,(
% 11.48/1.98    k1_xboole_0 = o_0_0_xboole_0),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f45,plain,(
% 11.48/1.98    k1_xboole_0 = o_0_0_xboole_0),
% 11.48/1.98    inference(cnf_transformation,[],[f2])).
% 11.48/1.98  
% 11.48/1.98  fof(f78,plain,(
% 11.48/1.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0) )),
% 11.48/1.98    inference(definition_unfolding,[],[f62,f45])).
% 11.48/1.98  
% 11.48/1.98  fof(f1,axiom,(
% 11.48/1.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f20,plain,(
% 11.48/1.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 11.48/1.98    inference(unused_predicate_definition_removal,[],[f1])).
% 11.48/1.98  
% 11.48/1.98  fof(f21,plain,(
% 11.48/1.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 11.48/1.98    inference(ennf_transformation,[],[f20])).
% 11.48/1.98  
% 11.48/1.98  fof(f44,plain,(
% 11.48/1.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f21])).
% 11.48/1.98  
% 11.48/1.98  fof(f12,axiom,(
% 11.48/1.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f28,plain,(
% 11.48/1.98    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 11.48/1.98    inference(ennf_transformation,[],[f12])).
% 11.48/1.98  
% 11.48/1.98  fof(f58,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 11.48/1.98    inference(cnf_transformation,[],[f28])).
% 11.48/1.98  
% 11.48/1.98  fof(f75,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 11.48/1.98    inference(definition_unfolding,[],[f58,f56])).
% 11.48/1.98  
% 11.48/1.98  fof(f70,plain,(
% 11.48/1.98    k1_xboole_0 != sK2),
% 11.48/1.98    inference(cnf_transformation,[],[f43])).
% 11.48/1.98  
% 11.48/1.98  fof(f84,plain,(
% 11.48/1.98    o_0_0_xboole_0 != sK2),
% 11.48/1.98    inference(definition_unfolding,[],[f70,f45])).
% 11.48/1.98  
% 11.48/1.98  fof(f71,plain,(
% 11.48/1.98    k1_xboole_0 != sK3),
% 11.48/1.98    inference(cnf_transformation,[],[f43])).
% 11.48/1.98  
% 11.48/1.98  fof(f83,plain,(
% 11.48/1.98    o_0_0_xboole_0 != sK3),
% 11.48/1.98    inference(definition_unfolding,[],[f71,f45])).
% 11.48/1.98  
% 11.48/1.98  fof(f72,plain,(
% 11.48/1.98    k1_xboole_0 != sK4),
% 11.48/1.98    inference(cnf_transformation,[],[f43])).
% 11.48/1.98  
% 11.48/1.98  fof(f82,plain,(
% 11.48/1.98    o_0_0_xboole_0 != sK4),
% 11.48/1.98    inference(definition_unfolding,[],[f72,f45])).
% 11.48/1.98  
% 11.48/1.98  fof(f3,axiom,(
% 11.48/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f19,plain,(
% 11.48/1.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 11.48/1.98    inference(unused_predicate_definition_removal,[],[f3])).
% 11.48/1.98  
% 11.48/1.98  fof(f22,plain,(
% 11.48/1.98    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 11.48/1.98    inference(ennf_transformation,[],[f19])).
% 11.48/1.98  
% 11.48/1.98  fof(f36,plain,(
% 11.48/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.48/1.98    introduced(choice_axiom,[])).
% 11.48/1.98  
% 11.48/1.98  fof(f37,plain,(
% 11.48/1.98    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.48/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f36])).
% 11.48/1.98  
% 11.48/1.98  fof(f46,plain,(
% 11.48/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f37])).
% 11.48/1.98  
% 11.48/1.98  fof(f8,axiom,(
% 11.48/1.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f26,plain,(
% 11.48/1.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.48/1.98    inference(ennf_transformation,[],[f8])).
% 11.48/1.98  
% 11.48/1.98  fof(f54,plain,(
% 11.48/1.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f26])).
% 11.48/1.98  
% 11.48/1.98  fof(f4,axiom,(
% 11.48/1.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f38,plain,(
% 11.48/1.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.48/1.98    inference(nnf_transformation,[],[f4])).
% 11.48/1.98  
% 11.48/1.98  fof(f39,plain,(
% 11.48/1.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.48/1.98    inference(flattening,[],[f38])).
% 11.48/1.98  
% 11.48/1.98  fof(f50,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f39])).
% 11.48/1.98  
% 11.48/1.98  fof(f13,axiom,(
% 11.48/1.98    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f29,plain,(
% 11.48/1.98    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 11.48/1.98    inference(ennf_transformation,[],[f13])).
% 11.48/1.98  
% 11.48/1.98  fof(f60,plain,(
% 11.48/1.98    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 11.48/1.98    inference(cnf_transformation,[],[f29])).
% 11.48/1.98  
% 11.48/1.98  fof(f5,axiom,(
% 11.48/1.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f23,plain,(
% 11.48/1.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 11.48/1.98    inference(ennf_transformation,[],[f5])).
% 11.48/1.98  
% 11.48/1.98  fof(f51,plain,(
% 11.48/1.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f23])).
% 11.48/1.98  
% 11.48/1.98  fof(f59,plain,(
% 11.48/1.98    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 11.48/1.98    inference(cnf_transformation,[],[f29])).
% 11.48/1.98  
% 11.48/1.98  fof(f69,plain,(
% 11.48/1.98    ( ! [X6,X7,X5] : (sK5 = X5 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f43])).
% 11.48/1.98  
% 11.48/1.98  fof(f9,axiom,(
% 11.48/1.98    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f55,plain,(
% 11.48/1.98    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 11.48/1.98    inference(cnf_transformation,[],[f9])).
% 11.48/1.98  
% 11.48/1.98  fof(f85,plain,(
% 11.48/1.98    ( ! [X6,X7,X5] : (sK5 = X5 | k4_tarski(k4_tarski(X5,X6),X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 11.48/1.98    inference(definition_unfolding,[],[f69,f55])).
% 11.48/1.98  
% 11.48/1.98  fof(f16,axiom,(
% 11.48/1.98    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f33,plain,(
% 11.48/1.98    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 11.48/1.98    inference(ennf_transformation,[],[f16])).
% 11.48/1.98  
% 11.48/1.98  fof(f65,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.48/1.98    inference(cnf_transformation,[],[f33])).
% 11.48/1.98  
% 11.48/1.98  fof(f81,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 11.48/1.98    inference(definition_unfolding,[],[f65,f56,f45,f45,f45])).
% 11.48/1.98  
% 11.48/1.98  fof(f73,plain,(
% 11.48/1.98    k5_mcart_1(sK2,sK3,sK4,sK6) != sK5),
% 11.48/1.98    inference(cnf_transformation,[],[f43])).
% 11.48/1.98  
% 11.48/1.98  fof(f11,axiom,(
% 11.48/1.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 11.48/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.98  
% 11.48/1.98  fof(f27,plain,(
% 11.48/1.98    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 11.48/1.98    inference(ennf_transformation,[],[f11])).
% 11.48/1.98  
% 11.48/1.98  fof(f57,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 11.48/1.98    inference(cnf_transformation,[],[f27])).
% 11.48/1.98  
% 11.48/1.98  fof(f74,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 11.48/1.98    inference(definition_unfolding,[],[f57,f56])).
% 11.48/1.98  
% 11.48/1.98  fof(f67,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.48/1.98    inference(cnf_transformation,[],[f33])).
% 11.48/1.98  
% 11.48/1.98  fof(f79,plain,(
% 11.48/1.98    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 11.48/1.98    inference(definition_unfolding,[],[f67,f56,f45,f45,f45])).
% 11.48/1.98  
% 11.48/1.98  cnf(c_26,negated_conjecture,
% 11.48/1.98      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 11.48/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_861,plain,
% 11.48/1.98      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_7,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_873,plain,
% 11.48/1.98      ( m1_subset_1(X0,X1) != iProver_top
% 11.48/1.98      | r2_hidden(X0,X1) = iProver_top
% 11.48/1.98      | v1_xboole_0(X1) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2627,plain,
% 11.48/1.98      ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_861,c_873]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_8,plain,
% 11.48/1.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.48/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_14,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,X1)
% 11.48/1.98      | ~ v1_relat_1(X1)
% 11.48/1.98      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 11.48/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_274,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,X1)
% 11.48/1.98      | k2_zfmisc_1(X2,X3) != X1
% 11.48/1.98      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 11.48/1.98      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_275,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 11.48/1.98      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 11.48/1.98      inference(unflattening,[status(thm)],[c_274]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_860,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 11.48/1.98      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2678,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2627,c_860]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_17,plain,
% 11.48/1.98      ( r2_hidden(sK1(X0),X0) | o_0_0_xboole_0 = X0 ),
% 11.48/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_866,plain,
% 11.48/1.98      ( o_0_0_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_0,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_878,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | v1_xboole_0(X1) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1312,plain,
% 11.48/1.98      ( o_0_0_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_866,c_878]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2938,plain,
% 11.48/1.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = o_0_0_xboole_0
% 11.48/1.98      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2678,c_1312]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_11,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.48/1.98      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 11.48/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_871,plain,
% 11.48/1.98      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 11.48/1.98      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3806,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 11.48/1.98      | m1_subset_1(X0,o_0_0_xboole_0) != iProver_top
% 11.48/1.98      | m1_subset_1(k7_mcart_1(sK2,sK3,sK4,X0),sK4) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2938,c_871]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_24,negated_conjecture,
% 11.48/1.98      ( o_0_0_xboole_0 != sK2 ),
% 11.48/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_23,negated_conjecture,
% 11.48/1.98      ( o_0_0_xboole_0 != sK3 ),
% 11.48/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_22,negated_conjecture,
% 11.48/1.98      ( o_0_0_xboole_0 != sK4 ),
% 11.48/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1045,plain,
% 11.48/1.98      ( r2_hidden(sK1(sK4),sK4) | o_0_0_xboole_0 = sK4 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1048,plain,
% 11.48/1.98      ( r2_hidden(sK1(sK3),sK3) | o_0_0_xboole_0 = sK3 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1051,plain,
% 11.48/1.98      ( r2_hidden(sK1(sK2),sK2) | o_0_0_xboole_0 = sK2 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2,plain,
% 11.48/1.98      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f46]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_9,plain,
% 11.48/1.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 11.48/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_304,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK0(X1,X0),X1) ),
% 11.48/1.98      inference(resolution,[status(thm)],[c_2,c_9]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1140,plain,
% 11.48/1.98      ( r2_hidden(sK0(sK4,sK1(sK4)),sK4) | ~ r2_hidden(sK1(sK4),sK4) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_304]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2698,plain,
% 11.48/1.98      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 11.48/1.98      | k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 11.48/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_2678]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,X1)
% 11.48/1.98      | ~ r2_hidden(X2,X3)
% 11.48/1.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 11.48/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1159,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,X1)
% 11.48/1.98      | r2_hidden(k4_tarski(X0,sK1(sK3)),k2_zfmisc_1(X1,sK3))
% 11.48/1.98      | ~ r2_hidden(sK1(sK3),sK3) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3303,plain,
% 11.48/1.98      ( r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3))
% 11.48/1.98      | ~ r2_hidden(sK1(sK3),sK3)
% 11.48/1.98      | ~ r2_hidden(sK1(sK2),sK2) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1159]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1456,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,X1)
% 11.48/1.98      | r2_hidden(k4_tarski(X0,sK0(sK4,sK1(sK4))),k2_zfmisc_1(X1,sK4))
% 11.48/1.98      | ~ r2_hidden(sK0(sK4,sK1(sK4)),sK4) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_5023,plain,
% 11.48/1.98      ( r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 11.48/1.98      | ~ r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3))
% 11.48/1.98      | ~ r2_hidden(sK0(sK4,sK1(sK4)),sK4) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1456]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2190,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 11.48/1.98      | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_36414,plain,
% 11.48/1.98      ( ~ r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 11.48/1.98      | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_2190]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_36477,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6 ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_3806,c_24,c_23,c_22,c_1045,c_1048,c_1051,c_1140,
% 11.48/1.98                 c_2698,c_3303,c_5023,c_36414]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_877,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | r2_hidden(X2,X3) != iProver_top
% 11.48/1.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_12,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 11.48/1.98      | r2_hidden(k2_mcart_1(X0),X2) ),
% 11.48/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_870,plain,
% 11.48/1.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.48/1.98      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3009,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | r2_hidden(X2,X3) != iProver_top
% 11.48/1.98      | r2_hidden(k2_mcart_1(k4_tarski(X2,X0)),X1) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_877,c_870]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_17977,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2627,c_3009]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_6,plain,
% 11.48/1.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_874,plain,
% 11.48/1.98      ( m1_subset_1(X0,X1) = iProver_top
% 11.48/1.98      | r2_hidden(X0,X1) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_18664,plain,
% 11.48/1.98      ( m1_subset_1(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
% 11.48/1.98      | r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_17977,c_874]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1046,plain,
% 11.48/1.98      ( o_0_0_xboole_0 = sK4 | r2_hidden(sK1(sK4),sK4) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1045]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1049,plain,
% 11.48/1.98      ( o_0_0_xboole_0 = sK3 | r2_hidden(sK1(sK3),sK3) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1048]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1052,plain,
% 11.48/1.98      ( o_0_0_xboole_0 = sK2 | r2_hidden(sK1(sK2),sK2) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1152,plain,
% 11.48/1.98      ( r2_hidden(sK0(sK4,sK1(sK4)),sK4) = iProver_top
% 11.48/1.98      | r2_hidden(sK1(sK4),sK4) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_1140]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3304,plain,
% 11.48/1.98      ( r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 11.48/1.98      | r2_hidden(sK1(sK3),sK3) != iProver_top
% 11.48/1.98      | r2_hidden(sK1(sK2),sK2) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_3303]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_5050,plain,
% 11.48/1.98      ( r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
% 11.48/1.98      | r2_hidden(k4_tarski(sK1(sK2),sK1(sK3)),k2_zfmisc_1(sK2,sK3)) != iProver_top
% 11.48/1.98      | r2_hidden(sK0(sK4,sK1(sK4)),sK4) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_5023]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_36415,plain,
% 11.48/1.98      ( r2_hidden(k4_tarski(k4_tarski(sK1(sK2),sK1(sK3)),sK0(sK4,sK1(sK4))),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) != iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_36414]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_40233,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | m1_subset_1(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_18664,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,
% 11.48/1.98                 c_3304,c_5050,c_36415]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_40234,plain,
% 11.48/1.98      ( m1_subset_1(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
% 11.48/1.98      | r2_hidden(X0,X1) != iProver_top ),
% 11.48/1.98      inference(renaming,[status(thm)],[c_40233]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_40239,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
% 11.48/1.98      | v1_xboole_0(X1) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_40234,c_873]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_43059,plain,
% 11.48/1.98      ( r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top
% 11.48/1.98      | r2_hidden(X0,X1) != iProver_top ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_40239,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,
% 11.48/1.98                 c_3304,c_5050,c_17977,c_36415]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_43060,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | r2_hidden(k2_mcart_1(k4_tarski(sK6,X0)),X1) = iProver_top ),
% 11.48/1.98      inference(renaming,[status(thm)],[c_43059]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_13,plain,
% 11.48/1.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 11.48/1.98      | r2_hidden(k1_mcart_1(X0),X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_869,plain,
% 11.48/1.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.48/1.98      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_43074,plain,
% 11.48/1.98      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.48/1.98      | r2_hidden(k1_mcart_1(k2_mcart_1(k4_tarski(sK6,X0))),X1) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_43060,c_869]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_45478,plain,
% 11.48/1.98      ( r2_hidden(k1_mcart_1(k2_mcart_1(k4_tarski(sK6,sK6))),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2627,c_43074]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_46609,plain,
% 11.48/1.98      ( r2_hidden(k1_mcart_1(k2_mcart_1(k4_tarski(sK6,sK6))),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_45478,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,
% 11.48/1.98                 c_3304,c_5050,c_36415]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2677,plain,
% 11.48/1.98      ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2627,c_869]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3352,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2677,c_860]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3004,plain,
% 11.48/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.48/1.98      | r2_hidden(X2,X3) != iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(X3,X1)) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_877,c_878]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_10830,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 11.48/1.98      | r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) != iProver_top
% 11.48/1.98      | r2_hidden(X1,sK4) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_3352,c_3004]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_46630,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 11.48/1.98      | r2_hidden(X0,sK4) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_46609,c_10830]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3382,plain,
% 11.48/1.98      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 11.48/1.98      | k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 11.48/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_3352]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_48575,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_46630,c_24,c_23,c_22,c_1045,c_1048,c_1051,c_1140,
% 11.48/1.98                 c_3303,c_3382,c_5023,c_36414]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_25,negated_conjecture,
% 11.48/1.98      ( ~ m1_subset_1(X0,sK4)
% 11.48/1.98      | ~ m1_subset_1(X1,sK3)
% 11.48/1.98      | ~ m1_subset_1(X2,sK2)
% 11.48/1.98      | k4_tarski(k4_tarski(X2,X1),X0) != sK6
% 11.48/1.98      | sK5 = X2 ),
% 11.48/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_862,plain,
% 11.48/1.98      ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
% 11.48/1.98      | sK5 = X0
% 11.48/1.98      | m1_subset_1(X2,sK4) != iProver_top
% 11.48/1.98      | m1_subset_1(X1,sK3) != iProver_top
% 11.48/1.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_48582,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 11.48/1.98      | k1_mcart_1(k1_mcart_1(sK6)) = sK5
% 11.48/1.98      | m1_subset_1(X0,sK4) != iProver_top
% 11.48/1.98      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
% 11.48/1.98      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_48575,c_862]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_20,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.48/1.98      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 11.48/1.98      | o_0_0_xboole_0 = X1
% 11.48/1.98      | o_0_0_xboole_0 = X2
% 11.48/1.98      | o_0_0_xboole_0 = X3 ),
% 11.48/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_863,plain,
% 11.48/1.98      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 11.48/1.98      | o_0_0_xboole_0 = X0
% 11.48/1.98      | o_0_0_xboole_0 = X1
% 11.48/1.98      | o_0_0_xboole_0 = X2
% 11.48/1.98      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2278,plain,
% 11.48/1.98      ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 11.48/1.98      | sK4 = o_0_0_xboole_0
% 11.48/1.98      | sK3 = o_0_0_xboole_0
% 11.48/1.98      | sK2 = o_0_0_xboole_0 ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_861,c_863]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_496,plain,( X0 = X0 ),theory(equality) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_513,plain,
% 11.48/1.98      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_496]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_497,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1061,plain,
% 11.48/1.98      ( sK4 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK4 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_497]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1062,plain,
% 11.48/1.98      ( sK4 != o_0_0_xboole_0
% 11.48/1.98      | o_0_0_xboole_0 = sK4
% 11.48/1.98      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1061]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1063,plain,
% 11.48/1.98      ( sK3 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK3 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_497]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1064,plain,
% 11.48/1.98      ( sK3 != o_0_0_xboole_0
% 11.48/1.98      | o_0_0_xboole_0 = sK3
% 11.48/1.98      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1063]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1065,plain,
% 11.48/1.98      ( sK2 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK2 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_497]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1066,plain,
% 11.48/1.98      ( sK2 != o_0_0_xboole_0
% 11.48/1.98      | o_0_0_xboole_0 = sK2
% 11.48/1.98      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1065]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2699,plain,
% 11.48/1.98      ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_2278,c_24,c_23,c_22,c_513,c_1062,c_1064,c_1066]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_21,negated_conjecture,
% 11.48/1.98      ( k5_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
% 11.48/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2702,plain,
% 11.48/1.98      ( k1_mcart_1(k1_mcart_1(sK6)) != sK5 ),
% 11.48/1.98      inference(demodulation,[status(thm)],[c_2699,c_21]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_10,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.48/1.98      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
% 11.48/1.98      inference(cnf_transformation,[],[f74]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_872,plain,
% 11.48/1.98      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 11.48/1.98      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2969,plain,
% 11.48/1.98      ( m1_subset_1(k5_mcart_1(sK2,sK3,sK4,sK6),sK2) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_861,c_872]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2976,plain,
% 11.48/1.98      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 11.48/1.98      inference(light_normalisation,[status(thm)],[c_2969,c_2699]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3350,plain,
% 11.48/1.98      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top
% 11.48/1.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_2677,c_870]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_10832,plain,
% 11.48/1.98      ( r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) != iProver_top
% 11.48/1.98      | r2_hidden(X1,sK4) != iProver_top
% 11.48/1.98      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_3350,c_3004]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_46631,plain,
% 11.48/1.98      ( r2_hidden(X0,sK4) != iProver_top
% 11.48/1.98      | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_46609,c_10832]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_48279,plain,
% 11.48/1.98      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_46631,c_24,c_23,c_22,c_1046,c_1049,c_1052,c_1152,
% 11.48/1.98                 c_3304,c_3350,c_5050,c_36415]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_48287,plain,
% 11.48/1.98      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_48279,c_874]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_48619,plain,
% 11.48/1.98      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 11.48/1.98      | m1_subset_1(X0,sK4) != iProver_top ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_48582,c_2702,c_2976,c_48287]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_48627,plain,
% 11.48/1.98      ( m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_36477,c_48619]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_18,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 11.48/1.98      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 11.48/1.98      | o_0_0_xboole_0 = X1
% 11.48/1.98      | o_0_0_xboole_0 = X2
% 11.48/1.98      | o_0_0_xboole_0 = X3 ),
% 11.48/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_865,plain,
% 11.48/1.98      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 11.48/1.98      | o_0_0_xboole_0 = X0
% 11.48/1.98      | o_0_0_xboole_0 = X1
% 11.48/1.98      | o_0_0_xboole_0 = X2
% 11.48/1.98      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 11.48/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3056,plain,
% 11.48/1.98      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 11.48/1.98      | sK4 = o_0_0_xboole_0
% 11.48/1.98      | sK3 = o_0_0_xboole_0
% 11.48/1.98      | sK2 = o_0_0_xboole_0 ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_861,c_865]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1110,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,X1),X2))
% 11.48/1.98      | k7_mcart_1(sK2,X1,X2,X0) = k2_mcart_1(X0)
% 11.48/1.98      | o_0_0_xboole_0 = X1
% 11.48/1.98      | o_0_0_xboole_0 = X2
% 11.48/1.98      | o_0_0_xboole_0 = sK2 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_18]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1365,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X1))
% 11.48/1.98      | k7_mcart_1(sK2,sK3,X1,X0) = k2_mcart_1(X0)
% 11.48/1.98      | o_0_0_xboole_0 = X1
% 11.48/1.98      | o_0_0_xboole_0 = sK3
% 11.48/1.98      | o_0_0_xboole_0 = sK2 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1110]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_1683,plain,
% 11.48/1.98      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 11.48/1.98      | k7_mcart_1(sK2,sK3,sK4,X0) = k2_mcart_1(X0)
% 11.48/1.98      | o_0_0_xboole_0 = sK4
% 11.48/1.98      | o_0_0_xboole_0 = sK3
% 11.48/1.98      | o_0_0_xboole_0 = sK2 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1365]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2657,plain,
% 11.48/1.98      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 11.48/1.98      | k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 11.48/1.98      | o_0_0_xboole_0 = sK4
% 11.48/1.98      | o_0_0_xboole_0 = sK3
% 11.48/1.98      | o_0_0_xboole_0 = sK2 ),
% 11.48/1.98      inference(instantiation,[status(thm)],[c_1683]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3143,plain,
% 11.48/1.98      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
% 11.48/1.98      inference(global_propositional_subsumption,
% 11.48/1.98                [status(thm)],
% 11.48/1.98                [c_3056,c_26,c_24,c_23,c_22,c_2657]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_2645,plain,
% 11.48/1.98      ( m1_subset_1(k7_mcart_1(sK2,sK3,sK4,sK6),sK4) = iProver_top ),
% 11.48/1.98      inference(superposition,[status(thm)],[c_861,c_871]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(c_3147,plain,
% 11.48/1.98      ( m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
% 11.48/1.98      inference(demodulation,[status(thm)],[c_3143,c_2645]) ).
% 11.48/1.98  
% 11.48/1.98  cnf(contradiction,plain,
% 11.48/1.98      ( $false ),
% 11.48/1.98      inference(minisat,[status(thm)],[c_48627,c_3147]) ).
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.48/1.98  
% 11.48/1.98  ------                               Statistics
% 11.48/1.98  
% 11.48/1.98  ------ General
% 11.48/1.98  
% 11.48/1.98  abstr_ref_over_cycles:                  0
% 11.48/1.98  abstr_ref_under_cycles:                 0
% 11.48/1.98  gc_basic_clause_elim:                   0
% 11.48/1.98  forced_gc_time:                         0
% 11.48/1.98  parsing_time:                           0.024
% 11.48/1.98  unif_index_cands_time:                  0.
% 11.48/1.98  unif_index_add_time:                    0.
% 11.48/1.98  orderings_time:                         0.
% 11.48/1.98  out_proof_time:                         0.019
% 11.48/1.98  total_time:                             1.211
% 11.48/1.98  num_of_symbols:                         52
% 11.48/1.98  num_of_terms:                           56538
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing
% 11.48/1.98  
% 11.48/1.98  num_of_splits:                          0
% 11.48/1.98  num_of_split_atoms:                     0
% 11.48/1.98  num_of_reused_defs:                     0
% 11.48/1.98  num_eq_ax_congr_red:                    50
% 11.48/1.98  num_of_sem_filtered_clauses:            1
% 11.48/1.98  num_of_subtypes:                        0
% 11.48/1.98  monotx_restored_types:                  0
% 11.48/1.98  sat_num_of_epr_types:                   0
% 11.48/1.98  sat_num_of_non_cyclic_types:            0
% 11.48/1.98  sat_guarded_non_collapsed_types:        0
% 11.48/1.98  num_pure_diseq_elim:                    0
% 11.48/1.98  simp_replaced_by:                       0
% 11.48/1.98  res_preprocessed:                       121
% 11.48/1.98  prep_upred:                             0
% 11.48/1.98  prep_unflattend:                        1
% 11.48/1.98  smt_new_axioms:                         0
% 11.48/1.98  pred_elim_cands:                        3
% 11.48/1.98  pred_elim:                              2
% 11.48/1.98  pred_elim_cl:                           2
% 11.48/1.98  pred_elim_cycles:                       5
% 11.48/1.98  merged_defs:                            0
% 11.48/1.98  merged_defs_ncl:                        0
% 11.48/1.98  bin_hyper_res:                          0
% 11.48/1.98  prep_cycles:                            4
% 11.48/1.98  pred_elim_time:                         0.002
% 11.48/1.98  splitting_time:                         0.
% 11.48/1.98  sem_filter_time:                        0.
% 11.48/1.98  monotx_time:                            0.001
% 11.48/1.98  subtype_inf_time:                       0.
% 11.48/1.98  
% 11.48/1.98  ------ Problem properties
% 11.48/1.98  
% 11.48/1.98  clauses:                                25
% 11.48/1.98  conjectures:                            6
% 11.48/1.98  epr:                                    6
% 11.48/1.98  horn:                                   20
% 11.48/1.98  ground:                                 5
% 11.48/1.98  unary:                                  5
% 11.48/1.98  binary:                                 12
% 11.48/1.98  lits:                                   61
% 11.48/1.98  lits_eq:                                24
% 11.48/1.98  fd_pure:                                0
% 11.48/1.98  fd_pseudo:                              0
% 11.48/1.98  fd_cond:                                7
% 11.48/1.98  fd_pseudo_cond:                         0
% 11.48/1.98  ac_symbols:                             0
% 11.48/1.98  
% 11.48/1.98  ------ Propositional Solver
% 11.48/1.98  
% 11.48/1.98  prop_solver_calls:                      32
% 11.48/1.98  prop_fast_solver_calls:                 1365
% 11.48/1.98  smt_solver_calls:                       0
% 11.48/1.98  smt_fast_solver_calls:                  0
% 11.48/1.98  prop_num_of_clauses:                    18032
% 11.48/1.98  prop_preprocess_simplified:             35449
% 11.48/1.98  prop_fo_subsumed:                       70
% 11.48/1.98  prop_solver_time:                       0.
% 11.48/1.98  smt_solver_time:                        0.
% 11.48/1.98  smt_fast_solver_time:                   0.
% 11.48/1.98  prop_fast_solver_time:                  0.
% 11.48/1.98  prop_unsat_core_time:                   0.002
% 11.48/1.98  
% 11.48/1.98  ------ QBF
% 11.48/1.98  
% 11.48/1.98  qbf_q_res:                              0
% 11.48/1.98  qbf_num_tautologies:                    0
% 11.48/1.98  qbf_prep_cycles:                        0
% 11.48/1.98  
% 11.48/1.98  ------ BMC1
% 11.48/1.98  
% 11.48/1.98  bmc1_current_bound:                     -1
% 11.48/1.98  bmc1_last_solved_bound:                 -1
% 11.48/1.98  bmc1_unsat_core_size:                   -1
% 11.48/1.98  bmc1_unsat_core_parents_size:           -1
% 11.48/1.98  bmc1_merge_next_fun:                    0
% 11.48/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.48/1.98  
% 11.48/1.98  ------ Instantiation
% 11.48/1.98  
% 11.48/1.98  inst_num_of_clauses:                    5287
% 11.48/1.98  inst_num_in_passive:                    3824
% 11.48/1.98  inst_num_in_active:                     1187
% 11.48/1.98  inst_num_in_unprocessed:                276
% 11.48/1.98  inst_num_of_loops:                      1340
% 11.48/1.98  inst_num_of_learning_restarts:          0
% 11.48/1.98  inst_num_moves_active_passive:          151
% 11.48/1.98  inst_lit_activity:                      0
% 11.48/1.98  inst_lit_activity_moves:                0
% 11.48/1.98  inst_num_tautologies:                   0
% 11.48/1.98  inst_num_prop_implied:                  0
% 11.48/1.98  inst_num_existing_simplified:           0
% 11.48/1.98  inst_num_eq_res_simplified:             0
% 11.48/1.98  inst_num_child_elim:                    0
% 11.48/1.98  inst_num_of_dismatching_blockings:      2407
% 11.48/1.98  inst_num_of_non_proper_insts:           3532
% 11.48/1.98  inst_num_of_duplicates:                 0
% 11.48/1.98  inst_inst_num_from_inst_to_res:         0
% 11.48/1.98  inst_dismatching_checking_time:         0.
% 11.48/1.98  
% 11.48/1.98  ------ Resolution
% 11.48/1.98  
% 11.48/1.98  res_num_of_clauses:                     0
% 11.48/1.98  res_num_in_passive:                     0
% 11.48/1.98  res_num_in_active:                      0
% 11.48/1.98  res_num_of_loops:                       125
% 11.48/1.98  res_forward_subset_subsumed:            54
% 11.48/1.98  res_backward_subset_subsumed:           0
% 11.48/1.98  res_forward_subsumed:                   0
% 11.48/1.98  res_backward_subsumed:                  0
% 11.48/1.98  res_forward_subsumption_resolution:     0
% 11.48/1.98  res_backward_subsumption_resolution:    0
% 11.48/1.98  res_clause_to_clause_subsumption:       7657
% 11.48/1.98  res_orphan_elimination:                 0
% 11.48/1.98  res_tautology_del:                      28
% 11.48/1.98  res_num_eq_res_simplified:              0
% 11.48/1.98  res_num_sel_changes:                    0
% 11.48/1.98  res_moves_from_active_to_pass:          0
% 11.48/1.98  
% 11.48/1.98  ------ Superposition
% 11.48/1.98  
% 11.48/1.98  sup_time_total:                         0.
% 11.48/1.98  sup_time_generating:                    0.
% 11.48/1.98  sup_time_sim_full:                      0.
% 11.48/1.98  sup_time_sim_immed:                     0.
% 11.48/1.98  
% 11.48/1.98  sup_num_of_clauses:                     1492
% 11.48/1.98  sup_num_in_active:                      241
% 11.48/1.98  sup_num_in_passive:                     1251
% 11.48/1.98  sup_num_of_loops:                       267
% 11.48/1.98  sup_fw_superposition:                   1332
% 11.48/1.98  sup_bw_superposition:                   1146
% 11.48/1.98  sup_immediate_simplified:               519
% 11.48/1.98  sup_given_eliminated:                   2
% 11.48/1.98  comparisons_done:                       0
% 11.48/1.98  comparisons_avoided:                    81
% 11.48/1.98  
% 11.48/1.98  ------ Simplifications
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  sim_fw_subset_subsumed:                 340
% 11.48/1.98  sim_bw_subset_subsumed:                 165
% 11.48/1.98  sim_fw_subsumed:                        144
% 11.48/1.98  sim_bw_subsumed:                        54
% 11.48/1.98  sim_fw_subsumption_res:                 0
% 11.48/1.98  sim_bw_subsumption_res:                 0
% 11.48/1.98  sim_tautology_del:                      10
% 11.48/1.98  sim_eq_tautology_del:                   3
% 11.48/1.98  sim_eq_res_simp:                        0
% 11.48/1.98  sim_fw_demodulated:                     0
% 11.48/1.98  sim_bw_demodulated:                     3
% 11.48/1.98  sim_light_normalised:                   1
% 11.48/1.98  sim_joinable_taut:                      0
% 11.48/1.98  sim_joinable_simp:                      0
% 11.48/1.98  sim_ac_normalised:                      0
% 11.48/1.98  sim_smt_subsumption:                    0
% 11.48/1.98  
%------------------------------------------------------------------------------
