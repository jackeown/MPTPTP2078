%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0482+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:24 EST 2020

% Result     : Theorem 22.02s
% Output     : CNFRefutation 22.02s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 169 expanded)
%              Number of clauses        :   58 (  59 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  571 ( 878 expanded)
%              Number of equality atoms :  124 ( 162 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK9(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK8(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK7(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK8(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f46,f49,f48,f47])).

fof(f75,plain,(
    ! [X2,X0,X5,X1] :
      ( k5_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X5,sK8(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).

fof(f63,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(k6_relat_1(X0),X1) != X1
        & r1_tarski(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k5_relat_1(k6_relat_1(sK11),sK12) != sK12
      & r1_tarski(k1_relat_1(sK12),sK11)
      & v1_relat_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k5_relat_1(k6_relat_1(sK11),sK12) != sK12
    & r1_tarski(k1_relat_1(sK12),sK11)
    & v1_relat_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f27,f52])).

fof(f87,plain,(
    k5_relat_1(k6_relat_1(sK11),sK12) != sK12 ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    r1_tarski(k1_relat_1(sK12),sK11) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21542,plain,
    ( ~ m1_subset_1(sK7(k6_relat_1(sK11),sK12,sK12),sK11)
    | r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),sK11)
    | v1_xboole_0(sK11) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_21548,plain,
    ( m1_subset_1(sK7(k6_relat_1(sK11),sK12,sK12),sK11) != iProver_top
    | r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),sK11) = iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21542])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_337,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_28,c_265])).

cnf(c_6708,plain,
    ( ~ r1_tarski(k1_relat_1(sK12),X0)
    | ~ r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_10671,plain,
    ( ~ r1_tarski(k1_relat_1(sK12),sK11)
    | ~ r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12))
    | ~ v1_xboole_0(sK11) ),
    inference(instantiation,[status(thm)],[c_6708])).

cnf(c_10672,plain,
    ( r1_tarski(k1_relat_1(sK12),sK11) != iProver_top
    | r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12)) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10671])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK8(X1,X2,X3)),X2)
    | ~ r2_hidden(k4_tarski(sK7(X1,X2,X3),X0),X1)
    | ~ r2_hidden(k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | k5_relat_1(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1962,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK8(k6_relat_1(sK11),sK12,sK12)),sK12)
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),X0),k6_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12)
    | ~ v1_relat_1(k6_relat_1(sK11))
    | ~ v1_relat_1(sK12)
    | k5_relat_1(k6_relat_1(sK11),sK12) = sK12 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9611,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK7(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12)
    | ~ v1_relat_1(k6_relat_1(sK11))
    | ~ v1_relat_1(sK12)
    | k5_relat_1(k6_relat_1(sK11),sK12) = sK12 ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_9612,plain,
    ( k5_relat_1(k6_relat_1(sK11),sK12) = sK12
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK7(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) != iProver_top
    | v1_relat_1(k6_relat_1(sK11)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9611])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X0)
    | r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2722,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),X0)
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),X1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8896,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK11),sK12),X0)
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),X0)
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),k5_relat_1(k6_relat_1(sK11),sK12))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK11),sK12)) ),
    inference(instantiation,[status(thm)],[c_2722])).

cnf(c_8908,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK11),sK12),X0) != iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),k5_relat_1(k6_relat_1(sK11),sK12)) != iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK11),sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8896])).

cnf(c_8910,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK11),sK12),sK12) != iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),k5_relat_1(k6_relat_1(sK11),sK12)) != iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) = iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK11),sK12)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8908])).

cnf(c_27,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2435,plain,
    ( m1_subset_1(sK7(k6_relat_1(sK11),sK12,sK12),X0)
    | ~ m1_subset_1(k1_relat_1(sK12),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_8878,plain,
    ( m1_subset_1(sK7(k6_relat_1(sK11),sK12,sK12),sK11)
    | ~ m1_subset_1(k1_relat_1(sK12),k1_zfmisc_1(sK11))
    | ~ r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_8879,plain,
    ( m1_subset_1(sK7(k6_relat_1(sK11),sK12,sK12),sK11) = iProver_top
    | m1_subset_1(k1_relat_1(sK12),k1_zfmisc_1(sK11)) != iProver_top
    | r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8878])).

cnf(c_3509,plain,
    ( m1_subset_1(k1_relat_1(sK12),k1_zfmisc_1(X0))
    | ~ r1_tarski(k1_relat_1(sK12),X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7493,plain,
    ( m1_subset_1(k1_relat_1(sK12),k1_zfmisc_1(sK11))
    | ~ r1_tarski(k1_relat_1(sK12),sK11) ),
    inference(instantiation,[status(thm)],[c_3509])).

cnf(c_7494,plain,
    ( m1_subset_1(k1_relat_1(sK12),k1_zfmisc_1(sK11)) = iProver_top
    | r1_tarski(k1_relat_1(sK12),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7493])).

cnf(c_19,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2540,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k6_relat_1(sK11),sK12,sK12),X0),X1)
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),X0),k5_relat_1(k6_relat_1(sK11),X1))
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK9(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK11),X1))
    | ~ v1_relat_1(k6_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5054,plain,
    ( ~ r2_hidden(k4_tarski(sK9(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12)
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK9(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11))
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),k5_relat_1(k6_relat_1(sK11),sK12))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK11),sK12))
    | ~ v1_relat_1(k6_relat_1(sK11))
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_2540])).

cnf(c_5055,plain,
    ( r2_hidden(k4_tarski(sK9(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) != iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK9(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),k5_relat_1(k6_relat_1(sK11),sK12)) = iProver_top
    | v1_relat_1(k5_relat_1(k6_relat_1(sK11),sK12)) != iProver_top
    | v1_relat_1(k6_relat_1(sK11)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5054])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4667,plain,
    ( ~ r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),sK11)
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK7(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11))
    | ~ v1_relat_1(k6_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4668,plain,
    ( r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK7(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11)) = iProver_top
    | v1_relat_1(k6_relat_1(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4667])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3291,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK11),sK12))
    | ~ v1_relat_1(k6_relat_1(sK11))
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3292,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK11),sK12)) = iProver_top
    | v1_relat_1(k6_relat_1(sK11)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3291])).

cnf(c_29,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2034,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK11),sK12),sK12)
    | ~ v1_relat_1(sK12) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2035,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK11),sK12),sK12) = iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1959,plain,
    ( r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12))
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1960,plain,
    ( r2_hidden(sK7(k6_relat_1(sK11),sK12,sK12),k1_relat_1(sK12)) = iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_23,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1762,plain,
    ( v1_relat_1(k6_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1763,plain,
    ( v1_relat_1(k6_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_18,plain,
    ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1745,plain,
    ( r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK9(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11))
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12)
    | ~ v1_relat_1(k6_relat_1(sK11))
    | ~ v1_relat_1(sK12)
    | k5_relat_1(k6_relat_1(sK11),sK12) = sK12 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1746,plain,
    ( k5_relat_1(k6_relat_1(sK11),sK12) = sK12
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK9(k6_relat_1(sK11),sK12,sK12)),k6_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) = iProver_top
    | v1_relat_1(k6_relat_1(sK11)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1745])).

cnf(c_17,plain,
    ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1742,plain,
    ( r2_hidden(k4_tarski(sK9(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12)
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12)
    | ~ v1_relat_1(k6_relat_1(sK11))
    | ~ v1_relat_1(sK12)
    | k5_relat_1(k6_relat_1(sK11),sK12) = sK12 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1743,plain,
    ( k5_relat_1(k6_relat_1(sK11),sK12) = sK12
    | r2_hidden(k4_tarski(sK9(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) = iProver_top
    | r2_hidden(k4_tarski(sK7(k6_relat_1(sK11),sK12,sK12),sK8(k6_relat_1(sK11),sK12,sK12)),sK12) = iProver_top
    | v1_relat_1(k6_relat_1(sK11)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1742])).

cnf(c_31,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK11),sK12) != sK12 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK12),sK11) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( r1_tarski(k1_relat_1(sK12),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,plain,
    ( v1_relat_1(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21548,c_10672,c_9612,c_8910,c_8879,c_7494,c_5055,c_4668,c_3292,c_2035,c_1960,c_1763,c_1746,c_1743,c_31,c_35,c_34])).


%------------------------------------------------------------------------------
