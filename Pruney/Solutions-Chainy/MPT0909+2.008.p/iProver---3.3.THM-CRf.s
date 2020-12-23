%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:54 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  195 (1305 expanded)
%              Number of clauses        :  106 ( 379 expanded)
%              Number of leaves         :   24 ( 304 expanded)
%              Depth                    :   22
%              Number of atoms          :  637 (6733 expanded)
%              Number of equality atoms :  381 (4170 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f46,plain,
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
   => ( k5_mcart_1(sK7,sK8,sK9,sK11) != sK10
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK10 = X5
                  | k3_mcart_1(X5,X6,X7) != sK11
                  | ~ m1_subset_1(X7,sK9) )
              | ~ m1_subset_1(X6,sK8) )
          | ~ m1_subset_1(X5,sK7) )
      & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k5_mcart_1(sK7,sK8,sK9,sK11) != sK10
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK10 = X5
                | k3_mcart_1(X5,X6,X7) != sK11
                | ~ m1_subset_1(X7,sK9) )
            | ~ m1_subset_1(X6,sK8) )
        | ~ m1_subset_1(X5,sK7) )
    & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f31,f46])).

fof(f82,plain,(
    m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,(
    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
    inference(definition_unfolding,[],[f82,f63])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f67,f63])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f47])).

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

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f42])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f63])).

fof(f84,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X6,X7,X5] :
      ( sK10 = X5
      | k3_mcart_1(X5,X6,X7) != sK11
      | ~ m1_subset_1(X7,sK9)
      | ~ m1_subset_1(X6,sK8)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f100,plain,(
    ! [X6,X7,X5] :
      ( sK10 = X5
      | k4_tarski(k4_tarski(X5,X6),X7) != sK11
      | ~ m1_subset_1(X7,sK9)
      | ~ m1_subset_1(X6,sK8)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(definition_unfolding,[],[f83,f62])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f63])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f63])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f88])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f78,f88])).

fof(f110,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f98])).

fof(f87,plain,(
    k5_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f75,f63])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f65,f63])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f37,f40,f39,f38])).

fof(f54,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f103,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f81,f88])).

fof(f107,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f95])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1126,plain,
    ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1136,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4063,plain,
    ( m1_subset_1(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1126,c_1136])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1139,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4494,plain,
    ( r2_hidden(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4063,c_1139])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_22,plain,
    ( r2_hidden(sK6(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1381,plain,
    ( r2_hidden(sK6(sK9),sK9)
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1382,plain,
    ( k1_xboole_0 = sK9
    | r2_hidden(sK6(sK9),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1492,plain,
    ( ~ r2_hidden(sK6(sK9),sK9)
    | ~ v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1496,plain,
    ( r2_hidden(sK6(sK9),sK9) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_5115,plain,
    ( r2_hidden(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4494,c_32,c_1382,c_1496])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1130,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4025,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1126,c_1130])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1470,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,X1),X2))
    | k7_mcart_1(sK7,X1,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1729,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X1))
    | k7_mcart_1(sK7,sK8,X1,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_2470,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
    | k7_mcart_1(sK7,sK8,sK9,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_3806,plain,
    ( ~ m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
    | k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2470])).

cnf(c_4496,plain,
    ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4025,c_36,c_34,c_33,c_32,c_3806])).

cnf(c_5119,plain,
    ( r2_hidden(k2_mcart_1(sK11),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5115,c_4496])).

cnf(c_1131,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK6(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2703,plain,
    ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1126,c_1139])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_334,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_1125,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_2911,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_1125])).

cnf(c_1150,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2446,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_1150])).

cnf(c_3942,plain,
    ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2911,c_2446])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1134,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2910,plain,
    ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_1134])).

cnf(c_3452,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2910,c_1125])).

cnf(c_3939,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3452,c_2446])).

cnf(c_35,negated_conjecture,
    ( ~ m1_subset_1(X0,sK9)
    | ~ m1_subset_1(X1,sK8)
    | ~ m1_subset_1(X2,sK7)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK11
    | sK10 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1127,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK11
    | sK10 = X0
    | m1_subset_1(X2,sK9) != iProver_top
    | m1_subset_1(X1,sK8) != iProver_top
    | m1_subset_1(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7279,plain,
    ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
    | k1_mcart_1(k1_mcart_1(sK11)) = sK10
    | m1_subset_1(X0,sK9) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3939,c_1127])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1128,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2195,plain,
    ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11))
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1126,c_1128])).

cnf(c_30,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_41,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_665,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1402,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1403,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1404,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1405,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_1406,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1407,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_2927,plain,
    ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2195,c_34,c_33,c_32,c_41,c_42,c_1403,c_1405,c_1407])).

cnf(c_31,negated_conjecture,
    ( k5_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2930,plain,
    ( k1_mcart_1(k1_mcart_1(sK11)) != sK10 ),
    inference(demodulation,[status(thm)],[c_2927,c_31])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1137,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4108,plain,
    ( m1_subset_1(k6_mcart_1(sK7,sK8,sK9,sK11),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1126,c_1137])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1129,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3622,plain,
    ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11))
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1126,c_1129])).

cnf(c_3800,plain,
    ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3622,c_34,c_33,c_32,c_41,c_42,c_1403,c_1405,c_1407])).

cnf(c_4140,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4108,c_3800])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1138,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4177,plain,
    ( m1_subset_1(k5_mcart_1(sK7,sK8,sK9,sK11),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1126,c_1138])).

cnf(c_4209,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4177,c_2927])).

cnf(c_7467,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK11),X0) != sK11
    | m1_subset_1(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7279,c_2930,c_4140,c_4209])).

cnf(c_7468,plain,
    ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
    | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
    | m1_subset_1(X0,sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_7467])).

cnf(c_7476,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK11),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3942,c_7468])).

cnf(c_4499,plain,
    ( m1_subset_1(k2_mcart_1(sK11),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4496,c_4063])).

cnf(c_7479,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7476,c_4499])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1144,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7495,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7479,c_1144])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1525,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1125])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_384,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_1977,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1525,c_384])).

cnf(c_8635,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7495,c_1977])).

cnf(c_8648,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_8635])).

cnf(c_1384,plain,
    ( r2_hidden(sK6(sK8),sK8)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1385,plain,
    ( k1_xboole_0 = sK8
    | r2_hidden(sK6(sK8),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_1387,plain,
    ( r2_hidden(sK6(sK7),sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1388,plain,
    ( k1_xboole_0 = sK7
    | r2_hidden(sK6(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1387])).

cnf(c_1502,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,sK6(sK8)),k2_zfmisc_1(X1,sK8))
    | ~ r2_hidden(sK6(sK8),sK8) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1914,plain,
    ( r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8))
    | ~ r2_hidden(sK6(sK8),sK8)
    | ~ r2_hidden(sK6(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_1915,plain,
    ( r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8)) = iProver_top
    | r2_hidden(sK6(sK8),sK8) != iProver_top
    | r2_hidden(sK6(sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_3132,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8))
    | ~ v1_xboole_0(k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3136,plain,
    ( r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3132])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1151,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8639,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_8635])).

cnf(c_9520,plain,
    ( r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8648,c_34,c_33,c_1385,c_1388,c_1915,c_3136,c_8639])).

cnf(c_9536,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5119,c_9520])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:34:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.67/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.98  
% 3.67/0.98  ------  iProver source info
% 3.67/0.98  
% 3.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.98  git: non_committed_changes: false
% 3.67/0.98  git: last_make_outside_of_git: false
% 3.67/0.98  
% 3.67/0.98  ------ 
% 3.67/0.98  
% 3.67/0.98  ------ Input Options
% 3.67/0.98  
% 3.67/0.98  --out_options                           all
% 3.67/0.98  --tptp_safe_out                         true
% 3.67/0.98  --problem_path                          ""
% 3.67/0.98  --include_path                          ""
% 3.67/0.98  --clausifier                            res/vclausify_rel
% 3.67/0.98  --clausifier_options                    --mode clausify
% 3.67/0.98  --stdin                                 false
% 3.67/0.98  --stats_out                             all
% 3.67/0.98  
% 3.67/0.98  ------ General Options
% 3.67/0.98  
% 3.67/0.98  --fof                                   false
% 3.67/0.98  --time_out_real                         305.
% 3.67/0.98  --time_out_virtual                      -1.
% 3.67/0.98  --symbol_type_check                     false
% 3.67/0.98  --clausify_out                          false
% 3.67/0.98  --sig_cnt_out                           false
% 3.67/0.98  --trig_cnt_out                          false
% 3.67/0.98  --trig_cnt_out_tolerance                1.
% 3.67/0.98  --trig_cnt_out_sk_spl                   false
% 3.67/0.98  --abstr_cl_out                          false
% 3.67/0.98  
% 3.67/0.98  ------ Global Options
% 3.67/0.98  
% 3.67/0.98  --schedule                              default
% 3.67/0.98  --add_important_lit                     false
% 3.67/0.98  --prop_solver_per_cl                    1000
% 3.67/0.98  --min_unsat_core                        false
% 3.67/0.98  --soft_assumptions                      false
% 3.67/0.98  --soft_lemma_size                       3
% 3.67/0.98  --prop_impl_unit_size                   0
% 3.67/0.98  --prop_impl_unit                        []
% 3.67/0.98  --share_sel_clauses                     true
% 3.67/0.98  --reset_solvers                         false
% 3.67/0.98  --bc_imp_inh                            [conj_cone]
% 3.67/0.98  --conj_cone_tolerance                   3.
% 3.67/0.98  --extra_neg_conj                        none
% 3.67/0.98  --large_theory_mode                     true
% 3.67/0.98  --prolific_symb_bound                   200
% 3.67/0.98  --lt_threshold                          2000
% 3.67/0.98  --clause_weak_htbl                      true
% 3.67/0.98  --gc_record_bc_elim                     false
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing Options
% 3.67/0.98  
% 3.67/0.98  --preprocessing_flag                    true
% 3.67/0.98  --time_out_prep_mult                    0.1
% 3.67/0.98  --splitting_mode                        input
% 3.67/0.98  --splitting_grd                         true
% 3.67/0.98  --splitting_cvd                         false
% 3.67/0.98  --splitting_cvd_svl                     false
% 3.67/0.98  --splitting_nvd                         32
% 3.67/0.98  --sub_typing                            true
% 3.67/0.98  --prep_gs_sim                           true
% 3.67/0.98  --prep_unflatten                        true
% 3.67/0.98  --prep_res_sim                          true
% 3.67/0.98  --prep_upred                            true
% 3.67/0.98  --prep_sem_filter                       exhaustive
% 3.67/0.98  --prep_sem_filter_out                   false
% 3.67/0.98  --pred_elim                             true
% 3.67/0.98  --res_sim_input                         true
% 3.67/0.98  --eq_ax_congr_red                       true
% 3.67/0.98  --pure_diseq_elim                       true
% 3.67/0.98  --brand_transform                       false
% 3.67/0.98  --non_eq_to_eq                          false
% 3.67/0.98  --prep_def_merge                        true
% 3.67/0.98  --prep_def_merge_prop_impl              false
% 3.67/0.98  --prep_def_merge_mbd                    true
% 3.67/0.98  --prep_def_merge_tr_red                 false
% 3.67/0.98  --prep_def_merge_tr_cl                  false
% 3.67/0.98  --smt_preprocessing                     true
% 3.67/0.98  --smt_ac_axioms                         fast
% 3.67/0.98  --preprocessed_out                      false
% 3.67/0.98  --preprocessed_stats                    false
% 3.67/0.98  
% 3.67/0.98  ------ Abstraction refinement Options
% 3.67/0.98  
% 3.67/0.98  --abstr_ref                             []
% 3.67/0.98  --abstr_ref_prep                        false
% 3.67/0.98  --abstr_ref_until_sat                   false
% 3.67/0.98  --abstr_ref_sig_restrict                funpre
% 3.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.98  --abstr_ref_under                       []
% 3.67/0.98  
% 3.67/0.98  ------ SAT Options
% 3.67/0.98  
% 3.67/0.98  --sat_mode                              false
% 3.67/0.98  --sat_fm_restart_options                ""
% 3.67/0.98  --sat_gr_def                            false
% 3.67/0.98  --sat_epr_types                         true
% 3.67/0.98  --sat_non_cyclic_types                  false
% 3.67/0.98  --sat_finite_models                     false
% 3.67/0.98  --sat_fm_lemmas                         false
% 3.67/0.98  --sat_fm_prep                           false
% 3.67/0.98  --sat_fm_uc_incr                        true
% 3.67/0.98  --sat_out_model                         small
% 3.67/0.98  --sat_out_clauses                       false
% 3.67/0.98  
% 3.67/0.98  ------ QBF Options
% 3.67/0.98  
% 3.67/0.98  --qbf_mode                              false
% 3.67/0.98  --qbf_elim_univ                         false
% 3.67/0.98  --qbf_dom_inst                          none
% 3.67/0.98  --qbf_dom_pre_inst                      false
% 3.67/0.98  --qbf_sk_in                             false
% 3.67/0.98  --qbf_pred_elim                         true
% 3.67/0.98  --qbf_split                             512
% 3.67/0.98  
% 3.67/0.98  ------ BMC1 Options
% 3.67/0.98  
% 3.67/0.98  --bmc1_incremental                      false
% 3.67/0.98  --bmc1_axioms                           reachable_all
% 3.67/0.98  --bmc1_min_bound                        0
% 3.67/0.98  --bmc1_max_bound                        -1
% 3.67/0.98  --bmc1_max_bound_default                -1
% 3.67/0.98  --bmc1_symbol_reachability              true
% 3.67/0.98  --bmc1_property_lemmas                  false
% 3.67/0.98  --bmc1_k_induction                      false
% 3.67/0.98  --bmc1_non_equiv_states                 false
% 3.67/0.98  --bmc1_deadlock                         false
% 3.67/0.98  --bmc1_ucm                              false
% 3.67/0.98  --bmc1_add_unsat_core                   none
% 3.67/0.98  --bmc1_unsat_core_children              false
% 3.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.98  --bmc1_out_stat                         full
% 3.67/0.98  --bmc1_ground_init                      false
% 3.67/0.98  --bmc1_pre_inst_next_state              false
% 3.67/0.98  --bmc1_pre_inst_state                   false
% 3.67/0.98  --bmc1_pre_inst_reach_state             false
% 3.67/0.98  --bmc1_out_unsat_core                   false
% 3.67/0.98  --bmc1_aig_witness_out                  false
% 3.67/0.98  --bmc1_verbose                          false
% 3.67/0.98  --bmc1_dump_clauses_tptp                false
% 3.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.98  --bmc1_dump_file                        -
% 3.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.98  --bmc1_ucm_extend_mode                  1
% 3.67/0.98  --bmc1_ucm_init_mode                    2
% 3.67/0.98  --bmc1_ucm_cone_mode                    none
% 3.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.98  --bmc1_ucm_relax_model                  4
% 3.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.98  --bmc1_ucm_layered_model                none
% 3.67/0.98  --bmc1_ucm_max_lemma_size               10
% 3.67/0.98  
% 3.67/0.98  ------ AIG Options
% 3.67/0.98  
% 3.67/0.98  --aig_mode                              false
% 3.67/0.98  
% 3.67/0.98  ------ Instantiation Options
% 3.67/0.98  
% 3.67/0.98  --instantiation_flag                    true
% 3.67/0.98  --inst_sos_flag                         false
% 3.67/0.98  --inst_sos_phase                        true
% 3.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel_side                     num_symb
% 3.67/0.98  --inst_solver_per_active                1400
% 3.67/0.98  --inst_solver_calls_frac                1.
% 3.67/0.98  --inst_passive_queue_type               priority_queues
% 3.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.98  --inst_passive_queues_freq              [25;2]
% 3.67/0.98  --inst_dismatching                      true
% 3.67/0.98  --inst_eager_unprocessed_to_passive     true
% 3.67/0.98  --inst_prop_sim_given                   true
% 3.67/0.98  --inst_prop_sim_new                     false
% 3.67/0.98  --inst_subs_new                         false
% 3.67/0.98  --inst_eq_res_simp                      false
% 3.67/0.98  --inst_subs_given                       false
% 3.67/0.98  --inst_orphan_elimination               true
% 3.67/0.98  --inst_learning_loop_flag               true
% 3.67/0.98  --inst_learning_start                   3000
% 3.67/0.98  --inst_learning_factor                  2
% 3.67/0.98  --inst_start_prop_sim_after_learn       3
% 3.67/0.98  --inst_sel_renew                        solver
% 3.67/0.98  --inst_lit_activity_flag                true
% 3.67/0.98  --inst_restr_to_given                   false
% 3.67/0.98  --inst_activity_threshold               500
% 3.67/0.98  --inst_out_proof                        true
% 3.67/0.98  
% 3.67/0.98  ------ Resolution Options
% 3.67/0.98  
% 3.67/0.98  --resolution_flag                       true
% 3.67/0.98  --res_lit_sel                           adaptive
% 3.67/0.98  --res_lit_sel_side                      none
% 3.67/0.98  --res_ordering                          kbo
% 3.67/0.98  --res_to_prop_solver                    active
% 3.67/0.98  --res_prop_simpl_new                    false
% 3.67/0.98  --res_prop_simpl_given                  true
% 3.67/0.98  --res_passive_queue_type                priority_queues
% 3.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.98  --res_passive_queues_freq               [15;5]
% 3.67/0.98  --res_forward_subs                      full
% 3.67/0.98  --res_backward_subs                     full
% 3.67/0.98  --res_forward_subs_resolution           true
% 3.67/0.98  --res_backward_subs_resolution          true
% 3.67/0.98  --res_orphan_elimination                true
% 3.67/0.98  --res_time_limit                        2.
% 3.67/0.98  --res_out_proof                         true
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Options
% 3.67/0.98  
% 3.67/0.98  --superposition_flag                    true
% 3.67/0.98  --sup_passive_queue_type                priority_queues
% 3.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.98  --demod_completeness_check              fast
% 3.67/0.98  --demod_use_ground                      true
% 3.67/0.98  --sup_to_prop_solver                    passive
% 3.67/0.98  --sup_prop_simpl_new                    true
% 3.67/0.98  --sup_prop_simpl_given                  true
% 3.67/0.98  --sup_fun_splitting                     false
% 3.67/0.98  --sup_smt_interval                      50000
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Simplification Setup
% 3.67/0.98  
% 3.67/0.98  --sup_indices_passive                   []
% 3.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.98  --sup_full_bw                           [BwDemod]
% 3.67/0.98  --sup_immed_triv                        [TrivRules]
% 3.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.98  --sup_immed_bw_main                     []
% 3.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.98  
% 3.67/0.98  ------ Combination Options
% 3.67/0.98  
% 3.67/0.98  --comb_res_mult                         3
% 3.67/0.98  --comb_sup_mult                         2
% 3.67/0.98  --comb_inst_mult                        10
% 3.67/0.98  
% 3.67/0.98  ------ Debug Options
% 3.67/0.98  
% 3.67/0.98  --dbg_backtrace                         false
% 3.67/0.98  --dbg_dump_prop_clauses                 false
% 3.67/0.98  --dbg_dump_prop_clauses_file            -
% 3.67/0.98  --dbg_out_stat                          false
% 3.67/0.98  ------ Parsing...
% 3.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  ------ Proving...
% 3.67/0.98  ------ Problem Properties 
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  clauses                                 36
% 3.67/0.98  conjectures                             6
% 3.67/0.98  EPR                                     6
% 3.67/0.98  Horn                                    26
% 3.67/0.98  unary                                   11
% 3.67/0.98  binary                                  12
% 3.67/0.98  lits                                    86
% 3.67/0.98  lits eq                                 40
% 3.67/0.98  fd_pure                                 0
% 3.67/0.98  fd_pseudo                               0
% 3.67/0.98  fd_cond                                 8
% 3.67/0.98  fd_pseudo_cond                          4
% 3.67/0.98  AC symbols                              0
% 3.67/0.98  
% 3.67/0.98  ------ Schedule dynamic 5 is on 
% 3.67/0.98  
% 3.67/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ 
% 3.67/0.98  Current options:
% 3.67/0.98  ------ 
% 3.67/0.98  
% 3.67/0.98  ------ Input Options
% 3.67/0.98  
% 3.67/0.98  --out_options                           all
% 3.67/0.98  --tptp_safe_out                         true
% 3.67/0.98  --problem_path                          ""
% 3.67/0.98  --include_path                          ""
% 3.67/0.98  --clausifier                            res/vclausify_rel
% 3.67/0.98  --clausifier_options                    --mode clausify
% 3.67/0.98  --stdin                                 false
% 3.67/0.98  --stats_out                             all
% 3.67/0.98  
% 3.67/0.98  ------ General Options
% 3.67/0.98  
% 3.67/0.98  --fof                                   false
% 3.67/0.98  --time_out_real                         305.
% 3.67/0.98  --time_out_virtual                      -1.
% 3.67/0.98  --symbol_type_check                     false
% 3.67/0.98  --clausify_out                          false
% 3.67/0.98  --sig_cnt_out                           false
% 3.67/0.98  --trig_cnt_out                          false
% 3.67/0.98  --trig_cnt_out_tolerance                1.
% 3.67/0.98  --trig_cnt_out_sk_spl                   false
% 3.67/0.98  --abstr_cl_out                          false
% 3.67/0.98  
% 3.67/0.98  ------ Global Options
% 3.67/0.98  
% 3.67/0.98  --schedule                              default
% 3.67/0.98  --add_important_lit                     false
% 3.67/0.98  --prop_solver_per_cl                    1000
% 3.67/0.98  --min_unsat_core                        false
% 3.67/0.98  --soft_assumptions                      false
% 3.67/0.98  --soft_lemma_size                       3
% 3.67/0.98  --prop_impl_unit_size                   0
% 3.67/0.98  --prop_impl_unit                        []
% 3.67/0.98  --share_sel_clauses                     true
% 3.67/0.98  --reset_solvers                         false
% 3.67/0.98  --bc_imp_inh                            [conj_cone]
% 3.67/0.98  --conj_cone_tolerance                   3.
% 3.67/0.98  --extra_neg_conj                        none
% 3.67/0.98  --large_theory_mode                     true
% 3.67/0.98  --prolific_symb_bound                   200
% 3.67/0.98  --lt_threshold                          2000
% 3.67/0.98  --clause_weak_htbl                      true
% 3.67/0.98  --gc_record_bc_elim                     false
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing Options
% 3.67/0.98  
% 3.67/0.98  --preprocessing_flag                    true
% 3.67/0.98  --time_out_prep_mult                    0.1
% 3.67/0.98  --splitting_mode                        input
% 3.67/0.98  --splitting_grd                         true
% 3.67/0.98  --splitting_cvd                         false
% 3.67/0.98  --splitting_cvd_svl                     false
% 3.67/0.98  --splitting_nvd                         32
% 3.67/0.98  --sub_typing                            true
% 3.67/0.98  --prep_gs_sim                           true
% 3.67/0.98  --prep_unflatten                        true
% 3.67/0.98  --prep_res_sim                          true
% 3.67/0.98  --prep_upred                            true
% 3.67/0.98  --prep_sem_filter                       exhaustive
% 3.67/0.98  --prep_sem_filter_out                   false
% 3.67/0.98  --pred_elim                             true
% 3.67/0.98  --res_sim_input                         true
% 3.67/0.98  --eq_ax_congr_red                       true
% 3.67/0.98  --pure_diseq_elim                       true
% 3.67/0.98  --brand_transform                       false
% 3.67/0.98  --non_eq_to_eq                          false
% 3.67/0.98  --prep_def_merge                        true
% 3.67/0.98  --prep_def_merge_prop_impl              false
% 3.67/0.98  --prep_def_merge_mbd                    true
% 3.67/0.98  --prep_def_merge_tr_red                 false
% 3.67/0.98  --prep_def_merge_tr_cl                  false
% 3.67/0.98  --smt_preprocessing                     true
% 3.67/0.98  --smt_ac_axioms                         fast
% 3.67/0.98  --preprocessed_out                      false
% 3.67/0.98  --preprocessed_stats                    false
% 3.67/0.98  
% 3.67/0.98  ------ Abstraction refinement Options
% 3.67/0.98  
% 3.67/0.98  --abstr_ref                             []
% 3.67/0.98  --abstr_ref_prep                        false
% 3.67/0.98  --abstr_ref_until_sat                   false
% 3.67/0.98  --abstr_ref_sig_restrict                funpre
% 3.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/0.98  --abstr_ref_under                       []
% 3.67/0.98  
% 3.67/0.98  ------ SAT Options
% 3.67/0.98  
% 3.67/0.98  --sat_mode                              false
% 3.67/0.98  --sat_fm_restart_options                ""
% 3.67/0.98  --sat_gr_def                            false
% 3.67/0.98  --sat_epr_types                         true
% 3.67/0.98  --sat_non_cyclic_types                  false
% 3.67/0.98  --sat_finite_models                     false
% 3.67/0.98  --sat_fm_lemmas                         false
% 3.67/0.98  --sat_fm_prep                           false
% 3.67/0.98  --sat_fm_uc_incr                        true
% 3.67/0.98  --sat_out_model                         small
% 3.67/0.98  --sat_out_clauses                       false
% 3.67/0.98  
% 3.67/0.98  ------ QBF Options
% 3.67/0.98  
% 3.67/0.98  --qbf_mode                              false
% 3.67/0.98  --qbf_elim_univ                         false
% 3.67/0.98  --qbf_dom_inst                          none
% 3.67/0.98  --qbf_dom_pre_inst                      false
% 3.67/0.98  --qbf_sk_in                             false
% 3.67/0.98  --qbf_pred_elim                         true
% 3.67/0.98  --qbf_split                             512
% 3.67/0.98  
% 3.67/0.98  ------ BMC1 Options
% 3.67/0.98  
% 3.67/0.98  --bmc1_incremental                      false
% 3.67/0.98  --bmc1_axioms                           reachable_all
% 3.67/0.98  --bmc1_min_bound                        0
% 3.67/0.98  --bmc1_max_bound                        -1
% 3.67/0.98  --bmc1_max_bound_default                -1
% 3.67/0.98  --bmc1_symbol_reachability              true
% 3.67/0.98  --bmc1_property_lemmas                  false
% 3.67/0.98  --bmc1_k_induction                      false
% 3.67/0.98  --bmc1_non_equiv_states                 false
% 3.67/0.98  --bmc1_deadlock                         false
% 3.67/0.98  --bmc1_ucm                              false
% 3.67/0.98  --bmc1_add_unsat_core                   none
% 3.67/0.98  --bmc1_unsat_core_children              false
% 3.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/0.98  --bmc1_out_stat                         full
% 3.67/0.98  --bmc1_ground_init                      false
% 3.67/0.98  --bmc1_pre_inst_next_state              false
% 3.67/0.98  --bmc1_pre_inst_state                   false
% 3.67/0.98  --bmc1_pre_inst_reach_state             false
% 3.67/0.98  --bmc1_out_unsat_core                   false
% 3.67/0.98  --bmc1_aig_witness_out                  false
% 3.67/0.98  --bmc1_verbose                          false
% 3.67/0.98  --bmc1_dump_clauses_tptp                false
% 3.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.67/0.98  --bmc1_dump_file                        -
% 3.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.67/0.98  --bmc1_ucm_extend_mode                  1
% 3.67/0.98  --bmc1_ucm_init_mode                    2
% 3.67/0.98  --bmc1_ucm_cone_mode                    none
% 3.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.67/0.98  --bmc1_ucm_relax_model                  4
% 3.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/0.98  --bmc1_ucm_layered_model                none
% 3.67/0.98  --bmc1_ucm_max_lemma_size               10
% 3.67/0.98  
% 3.67/0.98  ------ AIG Options
% 3.67/0.98  
% 3.67/0.98  --aig_mode                              false
% 3.67/0.98  
% 3.67/0.98  ------ Instantiation Options
% 3.67/0.98  
% 3.67/0.98  --instantiation_flag                    true
% 3.67/0.98  --inst_sos_flag                         false
% 3.67/0.98  --inst_sos_phase                        true
% 3.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/0.98  --inst_lit_sel_side                     none
% 3.67/0.98  --inst_solver_per_active                1400
% 3.67/0.98  --inst_solver_calls_frac                1.
% 3.67/0.98  --inst_passive_queue_type               priority_queues
% 3.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/0.98  --inst_passive_queues_freq              [25;2]
% 3.67/0.98  --inst_dismatching                      true
% 3.67/0.98  --inst_eager_unprocessed_to_passive     true
% 3.67/0.98  --inst_prop_sim_given                   true
% 3.67/0.98  --inst_prop_sim_new                     false
% 3.67/0.98  --inst_subs_new                         false
% 3.67/0.98  --inst_eq_res_simp                      false
% 3.67/0.98  --inst_subs_given                       false
% 3.67/0.98  --inst_orphan_elimination               true
% 3.67/0.98  --inst_learning_loop_flag               true
% 3.67/0.98  --inst_learning_start                   3000
% 3.67/0.98  --inst_learning_factor                  2
% 3.67/0.98  --inst_start_prop_sim_after_learn       3
% 3.67/0.98  --inst_sel_renew                        solver
% 3.67/0.98  --inst_lit_activity_flag                true
% 3.67/0.98  --inst_restr_to_given                   false
% 3.67/0.98  --inst_activity_threshold               500
% 3.67/0.98  --inst_out_proof                        true
% 3.67/0.98  
% 3.67/0.98  ------ Resolution Options
% 3.67/0.98  
% 3.67/0.98  --resolution_flag                       false
% 3.67/0.98  --res_lit_sel                           adaptive
% 3.67/0.98  --res_lit_sel_side                      none
% 3.67/0.98  --res_ordering                          kbo
% 3.67/0.98  --res_to_prop_solver                    active
% 3.67/0.98  --res_prop_simpl_new                    false
% 3.67/0.98  --res_prop_simpl_given                  true
% 3.67/0.98  --res_passive_queue_type                priority_queues
% 3.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/0.98  --res_passive_queues_freq               [15;5]
% 3.67/0.98  --res_forward_subs                      full
% 3.67/0.98  --res_backward_subs                     full
% 3.67/0.98  --res_forward_subs_resolution           true
% 3.67/0.98  --res_backward_subs_resolution          true
% 3.67/0.98  --res_orphan_elimination                true
% 3.67/0.98  --res_time_limit                        2.
% 3.67/0.98  --res_out_proof                         true
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Options
% 3.67/0.98  
% 3.67/0.98  --superposition_flag                    true
% 3.67/0.98  --sup_passive_queue_type                priority_queues
% 3.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.67/0.98  --demod_completeness_check              fast
% 3.67/0.98  --demod_use_ground                      true
% 3.67/0.98  --sup_to_prop_solver                    passive
% 3.67/0.98  --sup_prop_simpl_new                    true
% 3.67/0.98  --sup_prop_simpl_given                  true
% 3.67/0.98  --sup_fun_splitting                     false
% 3.67/0.98  --sup_smt_interval                      50000
% 3.67/0.98  
% 3.67/0.98  ------ Superposition Simplification Setup
% 3.67/0.98  
% 3.67/0.98  --sup_indices_passive                   []
% 3.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.98  --sup_full_bw                           [BwDemod]
% 3.67/0.98  --sup_immed_triv                        [TrivRules]
% 3.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.98  --sup_immed_bw_main                     []
% 3.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.67/0.98  
% 3.67/0.98  ------ Combination Options
% 3.67/0.98  
% 3.67/0.98  --comb_res_mult                         3
% 3.67/0.98  --comb_sup_mult                         2
% 3.67/0.98  --comb_inst_mult                        10
% 3.67/0.98  
% 3.67/0.98  ------ Debug Options
% 3.67/0.98  
% 3.67/0.98  --dbg_backtrace                         false
% 3.67/0.98  --dbg_dump_prop_clauses                 false
% 3.67/0.98  --dbg_dump_prop_clauses_file            -
% 3.67/0.98  --dbg_out_stat                          false
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  % SZS status Theorem for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98   Resolution empty clause
% 3.67/0.98  
% 3.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  fof(f18,conjecture,(
% 3.67/0.98    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f19,negated_conjecture,(
% 3.67/0.98    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.67/0.98    inference(negated_conjecture,[],[f18])).
% 3.67/0.98  
% 3.67/0.98  fof(f30,plain,(
% 3.67/0.98    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.67/0.98    inference(ennf_transformation,[],[f19])).
% 3.67/0.98  
% 3.67/0.98  fof(f31,plain,(
% 3.67/0.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.67/0.98    inference(flattening,[],[f30])).
% 3.67/0.98  
% 3.67/0.98  fof(f46,plain,(
% 3.67/0.98    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k5_mcart_1(sK7,sK8,sK9,sK11) != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & ! [X5] : (! [X6] : (! [X7] : (sK10 = X5 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) | ~m1_subset_1(X5,sK7)) & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9)))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f47,plain,(
% 3.67/0.98    k5_mcart_1(sK7,sK8,sK9,sK11) != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & ! [X5] : (! [X6] : (! [X7] : (sK10 = X5 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9)) | ~m1_subset_1(X6,sK8)) | ~m1_subset_1(X5,sK7)) & m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9))),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f31,f46])).
% 3.67/0.98  
% 3.67/0.98  fof(f82,plain,(
% 3.67/0.98    m1_subset_1(sK11,k3_zfmisc_1(sK7,sK8,sK9))),
% 3.67/0.98    inference(cnf_transformation,[],[f47])).
% 3.67/0.98  
% 3.67/0.98  fof(f8,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f63,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f8])).
% 3.67/0.98  
% 3.67/0.98  fof(f101,plain,(
% 3.67/0.98    m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))),
% 3.67/0.98    inference(definition_unfolding,[],[f82,f63])).
% 3.67/0.98  
% 3.67/0.98  fof(f12,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f24,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.67/0.98    inference(ennf_transformation,[],[f12])).
% 3.67/0.98  
% 3.67/0.98  fof(f67,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f24])).
% 3.67/0.98  
% 3.67/0.98  fof(f91,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f67,f63])).
% 3.67/0.98  
% 3.67/0.98  fof(f5,axiom,(
% 3.67/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f20,plain,(
% 3.67/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.67/0.98    inference(ennf_transformation,[],[f5])).
% 3.67/0.98  
% 3.67/0.98  fof(f21,plain,(
% 3.67/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.67/0.98    inference(flattening,[],[f20])).
% 3.67/0.98  
% 3.67/0.98  fof(f60,plain,(
% 3.67/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f21])).
% 3.67/0.98  
% 3.67/0.98  fof(f86,plain,(
% 3.67/0.98    k1_xboole_0 != sK9),
% 3.67/0.98    inference(cnf_transformation,[],[f47])).
% 3.67/0.98  
% 3.67/0.98  fof(f15,axiom,(
% 3.67/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f28,plain,(
% 3.67/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.67/0.98    inference(ennf_transformation,[],[f15])).
% 3.67/0.98  
% 3.67/0.98  fof(f42,plain,(
% 3.67/0.98    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f43,plain,(
% 3.67/0.98    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f42])).
% 3.67/0.98  
% 3.67/0.98  fof(f71,plain,(
% 3.67/0.98    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 3.67/0.98    inference(cnf_transformation,[],[f43])).
% 3.67/0.98  
% 3.67/0.98  fof(f1,axiom,(
% 3.67/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f32,plain,(
% 3.67/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.98    inference(nnf_transformation,[],[f1])).
% 3.67/0.98  
% 3.67/0.98  fof(f33,plain,(
% 3.67/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.98    inference(rectify,[],[f32])).
% 3.67/0.98  
% 3.67/0.98  fof(f34,plain,(
% 3.67/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f35,plain,(
% 3.67/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.67/0.98  
% 3.67/0.98  fof(f48,plain,(
% 3.67/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f35])).
% 3.67/0.98  
% 3.67/0.98  fof(f16,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f29,plain,(
% 3.67/0.98    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.67/0.98    inference(ennf_transformation,[],[f16])).
% 3.67/0.98  
% 3.67/0.98  fof(f76,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.98    inference(cnf_transformation,[],[f29])).
% 3.67/0.98  
% 3.67/0.98  fof(f92,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.98    inference(definition_unfolding,[],[f76,f63])).
% 3.67/0.98  
% 3.67/0.98  fof(f84,plain,(
% 3.67/0.98    k1_xboole_0 != sK7),
% 3.67/0.98    inference(cnf_transformation,[],[f47])).
% 3.67/0.98  
% 3.67/0.98  fof(f85,plain,(
% 3.67/0.98    k1_xboole_0 != sK8),
% 3.67/0.98    inference(cnf_transformation,[],[f47])).
% 3.67/0.98  
% 3.67/0.98  fof(f6,axiom,(
% 3.67/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f61,plain,(
% 3.67/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f6])).
% 3.67/0.98  
% 3.67/0.98  fof(f14,axiom,(
% 3.67/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f26,plain,(
% 3.67/0.98    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.67/0.98    inference(ennf_transformation,[],[f14])).
% 3.67/0.98  
% 3.67/0.98  fof(f27,plain,(
% 3.67/0.98    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.67/0.98    inference(flattening,[],[f26])).
% 3.67/0.98  
% 3.67/0.98  fof(f70,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f27])).
% 3.67/0.98  
% 3.67/0.98  fof(f13,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f25,plain,(
% 3.67/0.98    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.67/0.98    inference(ennf_transformation,[],[f13])).
% 3.67/0.98  
% 3.67/0.98  fof(f68,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f25])).
% 3.67/0.98  
% 3.67/0.98  fof(f83,plain,(
% 3.67/0.98    ( ! [X6,X7,X5] : (sK10 = X5 | k3_mcart_1(X5,X6,X7) != sK11 | ~m1_subset_1(X7,sK9) | ~m1_subset_1(X6,sK8) | ~m1_subset_1(X5,sK7)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f47])).
% 3.67/0.98  
% 3.67/0.98  fof(f7,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f62,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f7])).
% 3.67/0.98  
% 3.67/0.98  fof(f100,plain,(
% 3.67/0.98    ( ! [X6,X7,X5] : (sK10 = X5 | k4_tarski(k4_tarski(X5,X6),X7) != sK11 | ~m1_subset_1(X7,sK9) | ~m1_subset_1(X6,sK8) | ~m1_subset_1(X5,sK7)) )),
% 3.67/0.98    inference(definition_unfolding,[],[f83,f62])).
% 3.67/0.98  
% 3.67/0.98  fof(f74,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.98    inference(cnf_transformation,[],[f29])).
% 3.67/0.98  
% 3.67/0.98  fof(f94,plain,(
% 3.67/0.98    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.98    inference(definition_unfolding,[],[f74,f63])).
% 3.67/0.98  
% 3.67/0.98  fof(f17,axiom,(
% 3.67/0.98    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f44,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.67/0.98    inference(nnf_transformation,[],[f17])).
% 3.67/0.98  
% 3.67/0.98  fof(f45,plain,(
% 3.67/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.67/0.99    inference(flattening,[],[f44])).
% 3.67/0.99  
% 3.67/0.99  fof(f77,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f9,axiom,(
% 3.67/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f64,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f9])).
% 3.67/0.99  
% 3.67/0.99  fof(f88,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.67/0.99    inference(definition_unfolding,[],[f64,f63])).
% 3.67/0.99  
% 3.67/0.99  fof(f99,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.99    inference(definition_unfolding,[],[f77,f88])).
% 3.67/0.99  
% 3.67/0.99  fof(f78,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f98,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.67/0.99    inference(definition_unfolding,[],[f78,f88])).
% 3.67/0.99  
% 3.67/0.99  fof(f110,plain,(
% 3.67/0.99    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 3.67/0.99    inference(equality_resolution,[],[f98])).
% 3.67/0.99  
% 3.67/0.99  fof(f87,plain,(
% 3.67/0.99    k5_mcart_1(sK7,sK8,sK9,sK11) != sK10),
% 3.67/0.99    inference(cnf_transformation,[],[f47])).
% 3.67/0.99  
% 3.67/0.99  fof(f11,axiom,(
% 3.67/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 3.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f23,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.67/0.99    inference(ennf_transformation,[],[f11])).
% 3.67/0.99  
% 3.67/0.99  fof(f66,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f23])).
% 3.67/0.99  
% 3.67/0.99  fof(f90,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.67/0.99    inference(definition_unfolding,[],[f66,f63])).
% 3.67/0.99  
% 3.67/0.99  fof(f75,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.99    inference(cnf_transformation,[],[f29])).
% 3.67/0.99  
% 3.67/0.99  fof(f93,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.67/0.99    inference(definition_unfolding,[],[f75,f63])).
% 3.67/0.99  
% 3.67/0.99  fof(f10,axiom,(
% 3.67/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 3.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f22,plain,(
% 3.67/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.67/0.99    inference(ennf_transformation,[],[f10])).
% 3.67/0.99  
% 3.67/0.99  fof(f65,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.67/0.99    inference(cnf_transformation,[],[f22])).
% 3.67/0.99  
% 3.67/0.99  fof(f89,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.67/0.99    inference(definition_unfolding,[],[f65,f63])).
% 3.67/0.99  
% 3.67/0.99  fof(f3,axiom,(
% 3.67/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f36,plain,(
% 3.67/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.67/0.99    inference(nnf_transformation,[],[f3])).
% 3.67/0.99  
% 3.67/0.99  fof(f37,plain,(
% 3.67/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.67/0.99    inference(rectify,[],[f36])).
% 3.67/0.99  
% 3.67/0.99  fof(f40,plain,(
% 3.67/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f39,plain,(
% 3.67/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f38,plain,(
% 3.67/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.67/0.99    introduced(choice_axiom,[])).
% 3.67/0.99  
% 3.67/0.99  fof(f41,plain,(
% 3.67/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.67/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f37,f40,f39,f38])).
% 3.67/0.99  
% 3.67/0.99  fof(f54,plain,(
% 3.67/0.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.67/0.99    inference(cnf_transformation,[],[f41])).
% 3.67/0.99  
% 3.67/0.99  fof(f102,plain,(
% 3.67/0.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.67/0.99    inference(equality_resolution,[],[f54])).
% 3.67/0.99  
% 3.67/0.99  fof(f103,plain,(
% 3.67/0.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 3.67/0.99    inference(equality_resolution,[],[f102])).
% 3.67/0.99  
% 3.67/0.99  fof(f81,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f45])).
% 3.67/0.99  
% 3.67/0.99  fof(f95,plain,(
% 3.67/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.67/0.99    inference(definition_unfolding,[],[f81,f88])).
% 3.67/0.99  
% 3.67/0.99  fof(f107,plain,(
% 3.67/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 3.67/0.99    inference(equality_resolution,[],[f95])).
% 3.67/0.99  
% 3.67/0.99  fof(f2,axiom,(
% 3.67/0.99    v1_xboole_0(k1_xboole_0)),
% 3.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.99  
% 3.67/0.99  fof(f50,plain,(
% 3.67/0.99    v1_xboole_0(k1_xboole_0)),
% 3.67/0.99    inference(cnf_transformation,[],[f2])).
% 3.67/0.99  
% 3.67/0.99  fof(f49,plain,(
% 3.67/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.67/0.99    inference(cnf_transformation,[],[f35])).
% 3.67/0.99  
% 3.67/0.99  cnf(c_36,negated_conjecture,
% 3.67/0.99      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1126,plain,
% 3.67/0.99      ( m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_16,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.67/0.99      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.67/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1136,plain,
% 3.67/0.99      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.67/0.99      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4063,plain,
% 3.67/0.99      ( m1_subset_1(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1126,c_1136]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_12,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1139,plain,
% 3.67/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.67/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.67/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4494,plain,
% 3.67/0.99      ( r2_hidden(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top
% 3.67/0.99      | v1_xboole_0(sK9) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_4063,c_1139]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_32,negated_conjecture,
% 3.67/0.99      ( k1_xboole_0 != sK9 ),
% 3.67/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_22,plain,
% 3.67/0.99      ( r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1381,plain,
% 3.67/0.99      ( r2_hidden(sK6(sK9),sK9) | k1_xboole_0 = sK9 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1382,plain,
% 3.67/0.99      ( k1_xboole_0 = sK9 | r2_hidden(sK6(sK9),sK9) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1492,plain,
% 3.67/0.99      ( ~ r2_hidden(sK6(sK9),sK9) | ~ v1_xboole_0(sK9) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1496,plain,
% 3.67/0.99      ( r2_hidden(sK6(sK9),sK9) != iProver_top
% 3.67/0.99      | v1_xboole_0(sK9) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5115,plain,
% 3.67/0.99      ( r2_hidden(k7_mcart_1(sK7,sK8,sK9,sK11),sK9) = iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_4494,c_32,c_1382,c_1496]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_23,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.67/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X3
% 3.67/0.99      | k1_xboole_0 = X2 ),
% 3.67/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1130,plain,
% 3.67/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.67/0.99      | k1_xboole_0 = X0
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X2
% 3.67/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4025,plain,
% 3.67/0.99      ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
% 3.67/0.99      | sK9 = k1_xboole_0
% 3.67/0.99      | sK8 = k1_xboole_0
% 3.67/0.99      | sK7 = k1_xboole_0 ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1126,c_1130]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_34,negated_conjecture,
% 3.67/0.99      ( k1_xboole_0 != sK7 ),
% 3.67/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_33,negated_conjecture,
% 3.67/0.99      ( k1_xboole_0 != sK8 ),
% 3.67/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1470,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,X1),X2))
% 3.67/0.99      | k7_mcart_1(sK7,X1,X2,X0) = k2_mcart_1(X0)
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X2
% 3.67/0.99      | k1_xboole_0 = sK7 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1729,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X1))
% 3.67/0.99      | k7_mcart_1(sK7,sK8,X1,X0) = k2_mcart_1(X0)
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = sK8
% 3.67/0.99      | k1_xboole_0 = sK7 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1470]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2470,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
% 3.67/0.99      | k7_mcart_1(sK7,sK8,sK9,X0) = k2_mcart_1(X0)
% 3.67/0.99      | k1_xboole_0 = sK9
% 3.67/0.99      | k1_xboole_0 = sK8
% 3.67/0.99      | k1_xboole_0 = sK7 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1729]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3806,plain,
% 3.67/0.99      ( ~ m1_subset_1(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9))
% 3.67/0.99      | k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11)
% 3.67/0.99      | k1_xboole_0 = sK9
% 3.67/0.99      | k1_xboole_0 = sK8
% 3.67/0.99      | k1_xboole_0 = sK7 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_2470]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4496,plain,
% 3.67/0.99      ( k7_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(sK11) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_4025,c_36,c_34,c_33,c_32,c_3806]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_5119,plain,
% 3.67/0.99      ( r2_hidden(k2_mcart_1(sK11),sK9) = iProver_top ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_5115,c_4496]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1131,plain,
% 3.67/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK6(X0),X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2703,plain,
% 3.67/0.99      ( r2_hidden(sK11,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
% 3.67/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1126,c_1139]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_13,plain,
% 3.67/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_19,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1)
% 3.67/0.99      | ~ v1_relat_1(X1)
% 3.67/0.99      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_334,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1)
% 3.67/0.99      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.67/0.99      | k2_zfmisc_1(X2,X3) != X1 ),
% 3.67/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_335,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.67/0.99      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.67/0.99      inference(unflattening,[status(thm)],[c_334]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1125,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.67/0.99      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2911,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
% 3.67/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_2703,c_1125]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1150,plain,
% 3.67/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2446,plain,
% 3.67/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1131,c_1150]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3942,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(sK11),k2_mcart_1(sK11)) = sK11
% 3.67/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_2911,c_2446]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_18,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1134,plain,
% 3.67/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.67/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2910,plain,
% 3.67/0.99      ( r2_hidden(k1_mcart_1(sK11),k2_zfmisc_1(sK7,sK8)) = iProver_top
% 3.67/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_2703,c_1134]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3452,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.67/0.99      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_2910,c_1125]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3939,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK11)),k2_mcart_1(k1_mcart_1(sK11))) = k1_mcart_1(sK11)
% 3.67/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_3452,c_2446]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_35,negated_conjecture,
% 3.67/0.99      ( ~ m1_subset_1(X0,sK9)
% 3.67/0.99      | ~ m1_subset_1(X1,sK8)
% 3.67/0.99      | ~ m1_subset_1(X2,sK7)
% 3.67/0.99      | k4_tarski(k4_tarski(X2,X1),X0) != sK11
% 3.67/0.99      | sK10 = X2 ),
% 3.67/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1127,plain,
% 3.67/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) != sK11
% 3.67/0.99      | sK10 = X0
% 3.67/0.99      | m1_subset_1(X2,sK9) != iProver_top
% 3.67/0.99      | m1_subset_1(X1,sK8) != iProver_top
% 3.67/0.99      | m1_subset_1(X0,sK7) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7279,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
% 3.67/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
% 3.67/0.99      | k1_mcart_1(k1_mcart_1(sK11)) = sK10
% 3.67/0.99      | m1_subset_1(X0,sK9) != iProver_top
% 3.67/0.99      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) != iProver_top
% 3.67/0.99      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_3939,c_1127]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_25,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.67/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X3
% 3.67/0.99      | k1_xboole_0 = X2 ),
% 3.67/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1128,plain,
% 3.67/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.67/0.99      | k1_xboole_0 = X0
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X2
% 3.67/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2195,plain,
% 3.67/0.99      ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11))
% 3.67/0.99      | sK9 = k1_xboole_0
% 3.67/0.99      | sK8 = k1_xboole_0
% 3.67/0.99      | sK7 = k1_xboole_0 ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1126,c_1128]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_30,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.67/0.99      | k1_xboole_0 = X0
% 3.67/0.99      | k1_xboole_0 = X2
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X3 ),
% 3.67/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_41,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.67/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_29,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_42,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_665,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1402,plain,
% 3.67/0.99      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_665]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1403,plain,
% 3.67/0.99      ( sK9 != k1_xboole_0 | k1_xboole_0 = sK9 | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1402]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1404,plain,
% 3.67/0.99      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_665]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1405,plain,
% 3.67/0.99      ( sK8 != k1_xboole_0 | k1_xboole_0 = sK8 | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1404]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1406,plain,
% 3.67/0.99      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_665]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1407,plain,
% 3.67/0.99      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1406]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2927,plain,
% 3.67/0.99      ( k5_mcart_1(sK7,sK8,sK9,sK11) = k1_mcart_1(k1_mcart_1(sK11)) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_2195,c_34,c_33,c_32,c_41,c_42,c_1403,c_1405,c_1407]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_31,negated_conjecture,
% 3.67/0.99      ( k5_mcart_1(sK7,sK8,sK9,sK11) != sK10 ),
% 3.67/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2930,plain,
% 3.67/0.99      ( k1_mcart_1(k1_mcart_1(sK11)) != sK10 ),
% 3.67/0.99      inference(demodulation,[status(thm)],[c_2927,c_31]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_15,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.67/0.99      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
% 3.67/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1137,plain,
% 3.67/0.99      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.67/0.99      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4108,plain,
% 3.67/0.99      ( m1_subset_1(k6_mcart_1(sK7,sK8,sK9,sK11),sK8) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1126,c_1137]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_24,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.67/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X3
% 3.67/0.99      | k1_xboole_0 = X2 ),
% 3.67/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1129,plain,
% 3.67/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.67/0.99      | k1_xboole_0 = X0
% 3.67/0.99      | k1_xboole_0 = X1
% 3.67/0.99      | k1_xboole_0 = X2
% 3.67/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3622,plain,
% 3.67/0.99      ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11))
% 3.67/0.99      | sK9 = k1_xboole_0
% 3.67/0.99      | sK8 = k1_xboole_0
% 3.67/0.99      | sK7 = k1_xboole_0 ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1126,c_1129]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3800,plain,
% 3.67/0.99      ( k6_mcart_1(sK7,sK8,sK9,sK11) = k2_mcart_1(k1_mcart_1(sK11)) ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_3622,c_34,c_33,c_32,c_41,c_42,c_1403,c_1405,c_1407]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4140,plain,
% 3.67/0.99      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK11)),sK8) = iProver_top ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_4108,c_3800]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_14,plain,
% 3.67/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.67/0.99      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
% 3.67/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1138,plain,
% 3.67/0.99      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.67/0.99      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4177,plain,
% 3.67/0.99      ( m1_subset_1(k5_mcart_1(sK7,sK8,sK9,sK11),sK7) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1126,c_1138]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4209,plain,
% 3.67/0.99      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK11)),sK7) = iProver_top ),
% 3.67/0.99      inference(light_normalisation,[status(thm)],[c_4177,c_2927]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7467,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
% 3.67/0.99      | k4_tarski(k1_mcart_1(sK11),X0) != sK11
% 3.67/0.99      | m1_subset_1(X0,sK9) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_7279,c_2930,c_4140,c_4209]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7468,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(sK11),X0) != sK11
% 3.67/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
% 3.67/0.99      | m1_subset_1(X0,sK9) != iProver_top ),
% 3.67/0.99      inference(renaming,[status(thm)],[c_7467]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7476,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0
% 3.67/0.99      | m1_subset_1(k2_mcart_1(sK11),sK9) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_3942,c_7468]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_4499,plain,
% 3.67/0.99      ( m1_subset_1(k2_mcart_1(sK11),sK9) = iProver_top ),
% 3.67/0.99      inference(demodulation,[status(thm)],[c_4496,c_4063]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7479,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k1_xboole_0 ),
% 3.67/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7476,c_4499]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1)
% 3.67/0.99      | ~ r2_hidden(X2,X3)
% 3.67/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.67/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1144,plain,
% 3.67/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.67/0.99      | r2_hidden(X2,X3) != iProver_top
% 3.67/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_7495,plain,
% 3.67/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
% 3.67/0.99      | r2_hidden(X1,sK9) != iProver_top
% 3.67/0.99      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_7479,c_1144]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_26,plain,
% 3.67/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0 ),
% 3.67/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1525,plain,
% 3.67/0.99      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.67/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_26,c_1125]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_2,plain,
% 3.67/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_382,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.67/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_383,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.67/0.99      inference(unflattening,[status(thm)],[c_382]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_384,plain,
% 3.67/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1977,plain,
% 3.67/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1525,c_384]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8635,plain,
% 3.67/0.99      ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
% 3.67/0.99      | r2_hidden(X1,sK9) != iProver_top ),
% 3.67/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_7495,c_1977]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8648,plain,
% 3.67/0.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0 | r2_hidden(X0,sK9) != iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1131,c_8635]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1384,plain,
% 3.67/0.99      ( r2_hidden(sK6(sK8),sK8) | k1_xboole_0 = sK8 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1385,plain,
% 3.67/0.99      ( k1_xboole_0 = sK8 | r2_hidden(sK6(sK8),sK8) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1387,plain,
% 3.67/0.99      ( r2_hidden(sK6(sK7),sK7) | k1_xboole_0 = sK7 ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1388,plain,
% 3.67/0.99      ( k1_xboole_0 = sK7 | r2_hidden(sK6(sK7),sK7) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1387]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1502,plain,
% 3.67/0.99      ( ~ r2_hidden(X0,X1)
% 3.67/0.99      | r2_hidden(k4_tarski(X0,sK6(sK8)),k2_zfmisc_1(X1,sK8))
% 3.67/0.99      | ~ r2_hidden(sK6(sK8),sK8) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1914,plain,
% 3.67/0.99      ( r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8))
% 3.67/0.99      | ~ r2_hidden(sK6(sK8),sK8)
% 3.67/0.99      | ~ r2_hidden(sK6(sK7),sK7) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1502]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1915,plain,
% 3.67/0.99      ( r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8)) = iProver_top
% 3.67/0.99      | r2_hidden(sK6(sK8),sK8) != iProver_top
% 3.67/0.99      | r2_hidden(sK6(sK7),sK7) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3132,plain,
% 3.67/0.99      ( ~ r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8))
% 3.67/0.99      | ~ v1_xboole_0(k2_zfmisc_1(sK7,sK8)) ),
% 3.67/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_3136,plain,
% 3.67/0.99      ( r2_hidden(k4_tarski(sK6(sK7),sK6(sK8)),k2_zfmisc_1(sK7,sK8)) != iProver_top
% 3.67/0.99      | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_3132]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_0,plain,
% 3.67/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.67/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_1151,plain,
% 3.67/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 3.67/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_8639,plain,
% 3.67/0.99      ( r2_hidden(X0,sK9) != iProver_top
% 3.67/0.99      | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_1151,c_8635]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_9520,plain,
% 3.67/0.99      ( r2_hidden(X0,sK9) != iProver_top ),
% 3.67/0.99      inference(global_propositional_subsumption,
% 3.67/0.99                [status(thm)],
% 3.67/0.99                [c_8648,c_34,c_33,c_1385,c_1388,c_1915,c_3136,c_8639]) ).
% 3.67/0.99  
% 3.67/0.99  cnf(c_9536,plain,
% 3.67/0.99      ( $false ),
% 3.67/0.99      inference(superposition,[status(thm)],[c_5119,c_9520]) ).
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.99  
% 3.67/0.99  ------                               Statistics
% 3.67/0.99  
% 3.67/0.99  ------ General
% 3.67/0.99  
% 3.67/0.99  abstr_ref_over_cycles:                  0
% 3.67/0.99  abstr_ref_under_cycles:                 0
% 3.67/0.99  gc_basic_clause_elim:                   0
% 3.67/0.99  forced_gc_time:                         0
% 3.67/0.99  parsing_time:                           0.009
% 3.67/0.99  unif_index_cands_time:                  0.
% 3.67/0.99  unif_index_add_time:                    0.
% 3.67/0.99  orderings_time:                         0.
% 3.67/0.99  out_proof_time:                         0.013
% 3.67/0.99  total_time:                             0.291
% 3.67/0.99  num_of_symbols:                         56
% 3.67/0.99  num_of_terms:                           13381
% 3.67/0.99  
% 3.67/0.99  ------ Preprocessing
% 3.67/0.99  
% 3.67/0.99  num_of_splits:                          0
% 3.67/0.99  num_of_split_atoms:                     0
% 3.67/0.99  num_of_reused_defs:                     0
% 3.67/0.99  num_eq_ax_congr_red:                    87
% 3.67/0.99  num_of_sem_filtered_clauses:            1
% 3.67/0.99  num_of_subtypes:                        0
% 3.67/0.99  monotx_restored_types:                  0
% 3.67/0.99  sat_num_of_epr_types:                   0
% 3.67/0.99  sat_num_of_non_cyclic_types:            0
% 3.67/0.99  sat_guarded_non_collapsed_types:        0
% 3.67/0.99  num_pure_diseq_elim:                    0
% 3.67/0.99  simp_replaced_by:                       0
% 3.67/0.99  res_preprocessed:                       166
% 3.67/0.99  prep_upred:                             0
% 3.67/0.99  prep_unflattend:                        9
% 3.67/0.99  smt_new_axioms:                         0
% 3.67/0.99  pred_elim_cands:                        3
% 3.67/0.99  pred_elim:                              1
% 3.67/0.99  pred_elim_cl:                           1
% 3.67/0.99  pred_elim_cycles:                       3
% 3.67/0.99  merged_defs:                            0
% 3.67/0.99  merged_defs_ncl:                        0
% 3.67/0.99  bin_hyper_res:                          0
% 3.67/0.99  prep_cycles:                            4
% 3.67/0.99  pred_elim_time:                         0.003
% 3.67/0.99  splitting_time:                         0.
% 3.67/0.99  sem_filter_time:                        0.
% 3.67/0.99  monotx_time:                            0.
% 3.67/0.99  subtype_inf_time:                       0.
% 3.67/0.99  
% 3.67/0.99  ------ Problem properties
% 3.67/0.99  
% 3.67/0.99  clauses:                                36
% 3.67/0.99  conjectures:                            6
% 3.67/0.99  epr:                                    6
% 3.67/0.99  horn:                                   26
% 3.67/0.99  ground:                                 6
% 3.67/0.99  unary:                                  11
% 3.67/0.99  binary:                                 12
% 3.67/0.99  lits:                                   86
% 3.67/0.99  lits_eq:                                40
% 3.67/0.99  fd_pure:                                0
% 3.67/0.99  fd_pseudo:                              0
% 3.67/0.99  fd_cond:                                8
% 3.67/0.99  fd_pseudo_cond:                         4
% 3.67/0.99  ac_symbols:                             0
% 3.67/0.99  
% 3.67/0.99  ------ Propositional Solver
% 3.67/0.99  
% 3.67/0.99  prop_solver_calls:                      27
% 3.67/0.99  prop_fast_solver_calls:                 1105
% 3.67/0.99  smt_solver_calls:                       0
% 3.67/0.99  smt_fast_solver_calls:                  0
% 3.67/0.99  prop_num_of_clauses:                    4162
% 3.67/0.99  prop_preprocess_simplified:             11234
% 3.67/0.99  prop_fo_subsumed:                       39
% 3.67/0.99  prop_solver_time:                       0.
% 3.67/0.99  smt_solver_time:                        0.
% 3.67/0.99  smt_fast_solver_time:                   0.
% 3.67/0.99  prop_fast_solver_time:                  0.
% 3.67/0.99  prop_unsat_core_time:                   0.
% 3.67/0.99  
% 3.67/0.99  ------ QBF
% 3.67/0.99  
% 3.67/0.99  qbf_q_res:                              0
% 3.67/0.99  qbf_num_tautologies:                    0
% 3.67/0.99  qbf_prep_cycles:                        0
% 3.67/0.99  
% 3.67/0.99  ------ BMC1
% 3.67/0.99  
% 3.67/0.99  bmc1_current_bound:                     -1
% 3.67/0.99  bmc1_last_solved_bound:                 -1
% 3.67/0.99  bmc1_unsat_core_size:                   -1
% 3.67/0.99  bmc1_unsat_core_parents_size:           -1
% 3.67/0.99  bmc1_merge_next_fun:                    0
% 3.67/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.67/0.99  
% 3.67/0.99  ------ Instantiation
% 3.67/0.99  
% 3.67/0.99  inst_num_of_clauses:                    1530
% 3.67/0.99  inst_num_in_passive:                    356
% 3.67/0.99  inst_num_in_active:                     458
% 3.67/0.99  inst_num_in_unprocessed:                716
% 3.67/0.99  inst_num_of_loops:                      470
% 3.67/0.99  inst_num_of_learning_restarts:          0
% 3.67/0.99  inst_num_moves_active_passive:          11
% 3.67/0.99  inst_lit_activity:                      0
% 3.67/0.99  inst_lit_activity_moves:                0
% 3.67/0.99  inst_num_tautologies:                   0
% 3.67/0.99  inst_num_prop_implied:                  0
% 3.67/0.99  inst_num_existing_simplified:           0
% 3.67/0.99  inst_num_eq_res_simplified:             0
% 3.67/0.99  inst_num_child_elim:                    0
% 3.67/0.99  inst_num_of_dismatching_blockings:      258
% 3.67/0.99  inst_num_of_non_proper_insts:           1011
% 3.67/0.99  inst_num_of_duplicates:                 0
% 3.67/0.99  inst_inst_num_from_inst_to_res:         0
% 3.67/0.99  inst_dismatching_checking_time:         0.
% 3.67/0.99  
% 3.67/0.99  ------ Resolution
% 3.67/0.99  
% 3.67/0.99  res_num_of_clauses:                     0
% 3.67/0.99  res_num_in_passive:                     0
% 3.67/0.99  res_num_in_active:                      0
% 3.67/0.99  res_num_of_loops:                       170
% 3.67/0.99  res_forward_subset_subsumed:            25
% 3.67/0.99  res_backward_subset_subsumed:           0
% 3.67/0.99  res_forward_subsumed:                   0
% 3.67/0.99  res_backward_subsumed:                  0
% 3.67/0.99  res_forward_subsumption_resolution:     0
% 3.67/0.99  res_backward_subsumption_resolution:    0
% 3.67/0.99  res_clause_to_clause_subsumption:       378
% 3.67/0.99  res_orphan_elimination:                 0
% 3.67/0.99  res_tautology_del:                      13
% 3.67/0.99  res_num_eq_res_simplified:              0
% 3.67/0.99  res_num_sel_changes:                    0
% 3.67/0.99  res_moves_from_active_to_pass:          0
% 3.67/0.99  
% 3.67/0.99  ------ Superposition
% 3.67/0.99  
% 3.67/0.99  sup_time_total:                         0.
% 3.67/0.99  sup_time_generating:                    0.
% 3.67/0.99  sup_time_sim_full:                      0.
% 3.67/0.99  sup_time_sim_immed:                     0.
% 3.67/0.99  
% 3.67/0.99  sup_num_of_clauses:                     192
% 3.67/0.99  sup_num_in_active:                      72
% 3.67/0.99  sup_num_in_passive:                     120
% 3.67/0.99  sup_num_of_loops:                       92
% 3.67/0.99  sup_fw_superposition:                   184
% 3.67/0.99  sup_bw_superposition:                   174
% 3.67/0.99  sup_immediate_simplified:               83
% 3.67/0.99  sup_given_eliminated:                   1
% 3.67/0.99  comparisons_done:                       0
% 3.67/0.99  comparisons_avoided:                    20
% 3.67/0.99  
% 3.67/0.99  ------ Simplifications
% 3.67/0.99  
% 3.67/0.99  
% 3.67/0.99  sim_fw_subset_subsumed:                 30
% 3.67/0.99  sim_bw_subset_subsumed:                 13
% 3.67/0.99  sim_fw_subsumed:                        11
% 3.67/0.99  sim_bw_subsumed:                        6
% 3.67/0.99  sim_fw_subsumption_res:                 1
% 3.67/0.99  sim_bw_subsumption_res:                 0
% 3.67/0.99  sim_tautology_del:                      6
% 3.67/0.99  sim_eq_tautology_del:                   38
% 3.67/0.99  sim_eq_res_simp:                        5
% 3.67/0.99  sim_fw_demodulated:                     31
% 3.67/0.99  sim_bw_demodulated:                     16
% 3.67/0.99  sim_light_normalised:                   13
% 3.67/0.99  sim_joinable_taut:                      0
% 3.67/0.99  sim_joinable_simp:                      0
% 3.67/0.99  sim_ac_normalised:                      0
% 3.67/0.99  sim_smt_subsumption:                    0
% 3.67/0.99  
%------------------------------------------------------------------------------
