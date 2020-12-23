%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0506+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:27 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 201 expanded)
%              Number of clauses        :   58 (  73 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   19
%              Number of atoms          :  391 ( 899 expanded)
%              Number of equality atoms :   57 (  88 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
            & r2_hidden(sK0(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK0(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0)
                    & r2_hidden(sK0(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f34,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))
      & r1_tarski(sK4,sK5)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))
    & r1_tarski(sK4,sK5)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f30])).

fof(f48,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ~ r1_tarski(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f33,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_512,plain,
    ( ~ r2_hidden(X0_43,X1_43)
    | ~ r2_hidden(k4_tarski(X0_43,X0_44),X2_43)
    | r2_hidden(k4_tarski(X0_43,X0_44),k7_relat_1(X2_43,X1_43))
    | ~ v1_relat_1(X2_43)
    | ~ v1_relat_1(k7_relat_1(X2_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3545,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),X0_43)
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),X0_44),X1_43)
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),X0_44),k7_relat_1(X1_43,X0_43))
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(k7_relat_1(X1_43,X0_43)) ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_10583,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),X0_43)
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),X1_43)
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),k7_relat_1(X1_43,X0_43))
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(k7_relat_1(X1_43,X0_43)) ),
    inference(instantiation,[status(thm)],[c_3545])).

cnf(c_14882,plain,
    ( ~ r2_hidden(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK5)
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),k7_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),sK6)
    | ~ v1_relat_1(k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10583])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0_43,X1_43)
    | r2_hidden(X0_43,X1_43)
    | v1_xboole_0(X1_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_6646,plain,
    ( ~ m1_subset_1(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK5)
    | r2_hidden(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_506,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k7_relat_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5324,plain,
    ( v1_relat_1(k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_502,plain,
    ( m1_subset_1(X0_43,X1_43)
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X1_43))
    | ~ r2_hidden(X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1542,plain,
    ( m1_subset_1(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),X0_43)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0_43))
    | ~ r2_hidden(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_5192,plain,
    ( m1_subset_1(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(sK5))
    | ~ r2_hidden(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_500,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_993,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_508,plain,
    ( r1_tarski(X0_43,X1_43)
    | r2_hidden(k4_tarski(sK2(X0_43,X1_43),sK3(X0_43,X1_43)),X0_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_985,plain,
    ( r1_tarski(X0_43,X1_43) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0_43,X1_43),sK3(X0_43,X1_43)),X0_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_510,plain,
    ( r2_hidden(X0_43,X1_43)
    | ~ r2_hidden(k4_tarski(X0_43,X0_44),k7_relat_1(X2_43,X1_43))
    | ~ v1_relat_1(X2_43)
    | ~ v1_relat_1(k7_relat_1(X2_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_983,plain,
    ( r2_hidden(X0_43,X1_43) = iProver_top
    | r2_hidden(k4_tarski(X0_43,X0_44),k7_relat_1(X2_43,X1_43)) != iProver_top
    | v1_relat_1(X2_43) != iProver_top
    | v1_relat_1(k7_relat_1(X2_43,X1_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_987,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k7_relat_1(X0_43,X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_1056,plain,
    ( r2_hidden(X0_43,X1_43) = iProver_top
    | r2_hidden(k4_tarski(X0_43,X0_44),k7_relat_1(X2_43,X1_43)) != iProver_top
    | v1_relat_1(X2_43) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_983,c_987])).

cnf(c_1830,plain,
    ( r1_tarski(k7_relat_1(X0_43,X1_43),X2_43) = iProver_top
    | r2_hidden(sK2(k7_relat_1(X0_43,X1_43),X2_43),X1_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k7_relat_1(X0_43,X1_43)) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_1056])).

cnf(c_556,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k7_relat_1(X0_43,X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_3440,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | r2_hidden(sK2(k7_relat_1(X0_43,X1_43),X2_43),X1_43) = iProver_top
    | r1_tarski(k7_relat_1(X0_43,X1_43),X2_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1830,c_556])).

cnf(c_3441,plain,
    ( r1_tarski(k7_relat_1(X0_43,X1_43),X2_43) = iProver_top
    | r2_hidden(sK2(k7_relat_1(X0_43,X1_43),X2_43),X1_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_3440])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_141,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_183,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_142])).

cnf(c_498,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r2_hidden(X2_43,X0_43)
    | ~ v1_xboole_0(X1_43) ),
    inference(subtyping,[status(esa)],[c_183])).

cnf(c_995,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r2_hidden(X2_43,X0_43) != iProver_top
    | v1_xboole_0(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_3449,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(k7_relat_1(X2_43,X0_43),X3_43) = iProver_top
    | v1_xboole_0(X1_43) != iProver_top
    | v1_relat_1(X2_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_3441,c_995])).

cnf(c_3957,plain,
    ( r1_tarski(k7_relat_1(X0_43,sK4),X1_43) = iProver_top
    | v1_xboole_0(sK5) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_3449])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_501,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_992,plain,
    ( r1_tarski(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_4106,plain,
    ( v1_xboole_0(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3957,c_992])).

cnf(c_4134,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4106])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k7_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_511,plain,
    ( r2_hidden(k4_tarski(X0_43,X0_44),X1_43)
    | ~ r2_hidden(k4_tarski(X0_43,X0_44),k7_relat_1(X1_43,X2_43))
    | ~ v1_relat_1(X1_43)
    | ~ v1_relat_1(k7_relat_1(X1_43,X2_43)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1351,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),k7_relat_1(sK6,sK4))
    | r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),sK6)
    | ~ v1_relat_1(k7_relat_1(sK6,sK4))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_1348,plain,
    ( r2_hidden(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK4)
    | ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),k7_relat_1(sK6,sK4))
    | ~ v1_relat_1(k7_relat_1(sK6,sK4))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1233,plain,
    ( v1_relat_1(k7_relat_1(sK6,sK4))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_427,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_142,c_16])).

cnf(c_428,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_405,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(sK6,sK5) != X1
    | k7_relat_1(sK6,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_406,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),k7_relat_1(sK6,sK5))
    | ~ v1_relat_1(k7_relat_1(sK6,sK4)) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_395,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_relat_1(X0)
    | k7_relat_1(sK6,sK5) != X1
    | k7_relat_1(sK6,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_396,plain,
    ( r2_hidden(k4_tarski(sK2(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5)),sK3(k7_relat_1(sK6,sK4),k7_relat_1(sK6,sK5))),k7_relat_1(sK6,sK4))
    | ~ v1_relat_1(k7_relat_1(sK6,sK4)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14882,c_6646,c_5324,c_5192,c_4134,c_1351,c_1348,c_1233,c_428,c_406,c_396,c_17])).


%------------------------------------------------------------------------------
