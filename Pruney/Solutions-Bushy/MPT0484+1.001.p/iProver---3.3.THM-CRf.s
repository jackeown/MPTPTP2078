%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0484+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:25 EST 2020

% Result     : Theorem 46.75s
% Output     : CNFRefutation 46.75s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 185 expanded)
%              Number of clauses        :   52 (  55 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  571 ( 965 expanded)
%              Number of equality atoms :   79 ( 125 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f20,plain,(
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

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f53,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK10(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK10(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK9(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f50,f53,f52,f51])).

fof(f78,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f41])).

fof(f69,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f44,f47,f46,f45])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).

fof(f62,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f98,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f81,plain,(
    ! [X2,X0,X5,X1] :
      ( k5_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X5,sK8(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) != X1
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k5_relat_1(sK13,k6_relat_1(sK12)) != sK13
      & r1_tarski(k2_relat_1(sK13),sK12)
      & v1_relat_1(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k5_relat_1(sK13,k6_relat_1(sK12)) != sK13
    & r1_tarski(k2_relat_1(sK13),sK12)
    & v1_relat_1(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f31,f58])).

fof(f96,plain,(
    k5_relat_1(sK13,k6_relat_1(sK12)) != sK13 ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    r1_tarski(k2_relat_1(sK13),sK12) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    v1_relat_1(sK13) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_50289,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK9(sK13,k6_relat_1(sK12),sK13)),X1)
    | r2_hidden(k4_tarski(X0,sK8(sK13,k6_relat_1(sK12),sK13)),k5_relat_1(X1,k6_relat_1(sK12)))
    | ~ r2_hidden(k4_tarski(sK9(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),k6_relat_1(sK12))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(sK12)))
    | ~ v1_relat_1(k6_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_101379,plain,
    ( ~ r2_hidden(k4_tarski(sK9(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),k6_relat_1(sK12))
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK9(sK13,k6_relat_1(sK12),sK13)),sK13)
    | r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),k5_relat_1(sK13,k6_relat_1(sK12)))
    | ~ v1_relat_1(k5_relat_1(sK13,k6_relat_1(sK12)))
    | ~ v1_relat_1(k6_relat_1(sK12))
    | ~ v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_50289])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1695,plain,
    ( ~ m1_subset_1(X0,sK12)
    | r2_hidden(X0,sK12)
    | v1_xboole_0(sK12) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_77941,plain,
    ( ~ m1_subset_1(sK8(sK13,k6_relat_1(sK12),sK13),sK12)
    | r2_hidden(sK8(sK13,k6_relat_1(sK12),sK13),sK12)
    | v1_xboole_0(sK12) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_29,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2257,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,k2_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_16821,plain,
    ( m1_subset_1(sK8(sK13,k6_relat_1(sK12),sK13),X0)
    | ~ m1_subset_1(k2_relat_1(sK13),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK8(sK13,k6_relat_1(sK12),sK13),k2_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_45126,plain,
    ( m1_subset_1(sK8(sK13,k6_relat_1(sK12),sK13),sK12)
    | ~ m1_subset_1(k2_relat_1(sK13),k1_zfmisc_1(sK12))
    | ~ r2_hidden(sK8(sK13,k6_relat_1(sK12),sK13),k2_relat_1(sK13)) ),
    inference(instantiation,[status(thm)],[c_16821])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_9360,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK12))
    | ~ r1_tarski(X0,sK12) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_22517,plain,
    ( m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(sK12))
    | ~ r1_tarski(k2_relat_1(X0),sK12) ),
    inference(instantiation,[status(thm)],[c_9360])).

cnf(c_22521,plain,
    ( m1_subset_1(k2_relat_1(sK13),k1_zfmisc_1(sK12))
    | ~ r1_tarski(k2_relat_1(sK13),sK12) ),
    inference(instantiation,[status(thm)],[c_22517])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_286])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_30,c_287])).

cnf(c_1630,plain,
    ( ~ r1_tarski(k2_relat_1(sK13),sK12)
    | ~ r2_hidden(X0,k2_relat_1(sK13))
    | ~ v1_xboole_0(sK12) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_17482,plain,
    ( ~ r1_tarski(k2_relat_1(sK13),sK12)
    | ~ r2_hidden(sK3(sK13,k5_relat_1(sK13,k6_relat_1(sK12))),k2_relat_1(sK13))
    | ~ v1_xboole_0(sK12) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X0)
    | r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1709,plain,
    ( ~ r1_tarski(X0,sK13)
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),X1),X0)
    | r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),X1),sK13)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2125,plain,
    ( ~ r1_tarski(k5_relat_1(X0,X1),sK13)
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),X2),k5_relat_1(X0,X1))
    | r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),X2),sK13)
    | ~ v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_3542,plain,
    ( ~ r1_tarski(k5_relat_1(sK13,k6_relat_1(sK12)),sK13)
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),X0),k5_relat_1(sK13,k6_relat_1(sK12)))
    | r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),X0),sK13)
    | ~ v1_relat_1(k5_relat_1(sK13,k6_relat_1(sK12))) ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_8733,plain,
    ( ~ r1_tarski(k5_relat_1(sK13,k6_relat_1(sK12)),sK13)
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),k5_relat_1(sK13,k6_relat_1(sK12)))
    | r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),sK13)
    | ~ v1_relat_1(k5_relat_1(sK13,k6_relat_1(sK12))) ),
    inference(instantiation,[status(thm)],[c_3542])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3981,plain,
    ( r2_hidden(X0,k2_relat_1(sK13))
    | ~ r2_hidden(k4_tarski(X1,X0),sK13) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7809,plain,
    ( r2_hidden(sK3(sK13,k5_relat_1(sK13,k6_relat_1(sK12))),k2_relat_1(sK13))
    | ~ r2_hidden(k4_tarski(sK2(sK13,k5_relat_1(sK13,k6_relat_1(sK12))),sK3(sK13,k5_relat_1(sK13,k6_relat_1(sK12)))),sK13) ),
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_7805,plain,
    ( r2_hidden(sK8(sK13,k6_relat_1(sK12),sK13),k2_relat_1(sK13))
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),sK13) ),
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2378,plain,
    ( v1_relat_1(k5_relat_1(sK13,k6_relat_1(sK12)))
    | ~ v1_relat_1(k6_relat_1(sK12))
    | ~ v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1859,plain,
    ( ~ r2_hidden(sK8(sK13,k6_relat_1(sK12),sK13),sK12)
    | r2_hidden(k4_tarski(sK8(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),k6_relat_1(sK12))
    | ~ v1_relat_1(k6_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK8(X1,X2,X3)),X2)
    | ~ r2_hidden(k4_tarski(sK7(X1,X2,X3),X0),X1)
    | ~ r2_hidden(k4_tarski(sK7(X1,X2,X3),sK8(X1,X2,X3)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | k5_relat_1(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1612,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK8(sK13,k6_relat_1(sK12),sK13)),k6_relat_1(sK12))
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),X0),sK13)
    | ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),sK13)
    | ~ v1_relat_1(k6_relat_1(sK12))
    | ~ v1_relat_1(sK13)
    | k5_relat_1(sK13,k6_relat_1(sK12)) = sK13 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1765,plain,
    ( ~ r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),sK13)
    | ~ r2_hidden(k4_tarski(sK8(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),k6_relat_1(sK12))
    | ~ v1_relat_1(k6_relat_1(sK12))
    | ~ v1_relat_1(sK13)
    | k5_relat_1(sK13,k6_relat_1(sK12)) = sK13 ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1751,plain,
    ( r1_tarski(sK13,k5_relat_1(sK13,k6_relat_1(sK12)))
    | r2_hidden(k4_tarski(sK2(sK13,k5_relat_1(sK13,k6_relat_1(sK12))),sK3(sK13,k5_relat_1(sK13,k6_relat_1(sK12)))),sK13)
    | ~ v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_23,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1661,plain,
    ( v1_relat_1(k6_relat_1(sK12)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_32,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1644,plain,
    ( r1_tarski(k5_relat_1(sK13,k6_relat_1(sK12)),sK13)
    | ~ v1_relat_1(sK13) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( r2_hidden(k4_tarski(sK9(X0,X1,X2),sK8(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1617,plain,
    ( r2_hidden(k4_tarski(sK9(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),k6_relat_1(sK12))
    | r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),sK13)
    | ~ v1_relat_1(k6_relat_1(sK12))
    | ~ v1_relat_1(sK13)
    | k5_relat_1(sK13,k6_relat_1(sK12)) = sK13 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK9(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1618,plain,
    ( r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK9(sK13,k6_relat_1(sK12),sK13)),sK13)
    | r2_hidden(k4_tarski(sK7(sK13,k6_relat_1(sK12),sK13),sK8(sK13,k6_relat_1(sK12),sK13)),sK13)
    | ~ v1_relat_1(k6_relat_1(sK12))
    | ~ v1_relat_1(sK13)
    | k5_relat_1(sK13,k6_relat_1(sK12)) = sK13 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1602,plain,
    ( ~ r1_tarski(k5_relat_1(sK13,k6_relat_1(sK12)),sK13)
    | ~ r1_tarski(sK13,k5_relat_1(sK13,k6_relat_1(sK12)))
    | k5_relat_1(sK13,k6_relat_1(sK12)) = sK13 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_34,negated_conjecture,
    ( k5_relat_1(sK13,k6_relat_1(sK12)) != sK13 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK13),sK12) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_36,negated_conjecture,
    ( v1_relat_1(sK13) ),
    inference(cnf_transformation,[],[f94])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_101379,c_77941,c_45126,c_22521,c_17482,c_8733,c_7809,c_7805,c_2378,c_1859,c_1765,c_1751,c_1661,c_1644,c_1617,c_1618,c_1602,c_34,c_35,c_36])).


%------------------------------------------------------------------------------
