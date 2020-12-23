%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:51 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 309 expanded)
%              Number of clauses        :   89 ( 134 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  449 (1155 expanded)
%              Number of equality atoms :  199 ( 372 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1)
        & r2_hidden(sK0(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | r2_hidden(sK0(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & ( r1_tarski(sK1(X0,X1),sK2(X0,X1))
              | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
            & r2_hidden(sK2(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f39])).

fof(f62,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3)) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ~ r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f41])).

fof(f68,plain,(
    ~ r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(k6_relat_1(X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_813,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_821,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
    | ~ r1_tarski(X2,X0)
    | ~ v1_relat_1(k1_wellord2(X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_804,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1)
    | r1_tarski(k6_relat_1(X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_814,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3248,plain,
    ( r2_hidden(sK0(X0,k1_wellord2(X1)),X1) != iProver_top
    | r1_tarski(sK0(X0,k1_wellord2(X1)),sK0(X0,k1_wellord2(X1))) != iProver_top
    | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) = iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_814])).

cnf(c_9302,plain,
    ( r2_hidden(sK0(X0,k1_wellord2(X1)),X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) = iProver_top
    | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_3248])).

cnf(c_9587,plain,
    ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_9302])).

cnf(c_24,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9592,plain,
    ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9587,c_27])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_815,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4855,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_815])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_57,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4935,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4855,c_57])).

cnf(c_4936,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4935])).

cnf(c_9601,plain,
    ( r1_tarski(X0,k1_relat_1(k1_wellord2(X0))) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9592,c_4936])).

cnf(c_9610,plain,
    ( r1_tarski(sK3,k1_relat_1(k1_wellord2(sK3))) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9601])).

cnf(c_9,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_816,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4878,plain,
    ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_816])).

cnf(c_5738,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k2_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4878,c_57])).

cnf(c_5739,plain,
    ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5738])).

cnf(c_9600,plain,
    ( r1_tarski(X0,k2_relat_1(k1_wellord2(X0))) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9592,c_5739])).

cnf(c_9607,plain,
    ( r1_tarski(sK3,k2_relat_1(k1_wellord2(sK3))) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9600])).

cnf(c_802,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_819,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1424,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = k3_relat_1(k1_wellord2(X0)) ),
    inference(superposition,[status(thm)],[c_802,c_819])).

cnf(c_23,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_147,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_24])).

cnf(c_1425,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1424,c_147])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_820,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_812,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2491,plain,
    ( k7_relat_1(X0,k2_xboole_0(k1_relat_1(X0),X1)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_820,c_812])).

cnf(c_4359,plain,
    ( k7_relat_1(k1_wellord2(X0),k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X1)) = k1_wellord2(X0) ),
    inference(superposition,[status(thm)],[c_802,c_2491])).

cnf(c_4995,plain,
    ( k7_relat_1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
    inference(superposition,[status(thm)],[c_1425,c_4359])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_810,plain,
    ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2019,plain,
    ( k8_relat_1(X0,k7_relat_1(k1_wellord2(X1),X0)) = k2_wellord1(k1_wellord2(X1),X0) ),
    inference(superposition,[status(thm)],[c_802,c_810])).

cnf(c_5001,plain,
    ( k2_wellord1(k1_wellord2(X0),X0) = k8_relat_1(X0,k1_wellord2(X0)) ),
    inference(superposition,[status(thm)],[c_4995,c_2019])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,k3_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_809,plain,
    ( k2_wellord1(X0,k3_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1281,plain,
    ( k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0))) = k1_wellord2(X0) ),
    inference(superposition,[status(thm)],[c_802,c_809])).

cnf(c_1282,plain,
    ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
    inference(light_normalisation,[status(thm)],[c_1281,c_147])).

cnf(c_5002,plain,
    ( k8_relat_1(X0,k1_wellord2(X0)) = k1_wellord2(X0) ),
    inference(light_normalisation,[status(thm)],[c_5001,c_1282])).

cnf(c_5,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_818,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5147,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5002,c_818])).

cnf(c_5149,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(sK3)),sK3) = iProver_top
    | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5147])).

cnf(c_445,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2737,plain,
    ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))) = k2_zfmisc_1(sK3,sK3)
    | k2_relat_1(k1_wellord2(sK3)) != sK3
    | k1_relat_1(k1_wellord2(sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_1841,plain,
    ( r1_tarski(k1_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1425,c_820])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_822,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2469,plain,
    ( k1_relat_1(k1_wellord2(X0)) = X0
    | r1_tarski(X0,k1_relat_1(k1_wellord2(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_822])).

cnf(c_2484,plain,
    ( k1_relat_1(k1_wellord2(sK3)) = sK3
    | r1_tarski(sK3,k1_relat_1(k1_wellord2(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2469])).

cnf(c_437,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_947,plain,
    ( X0 != X1
    | k2_zfmisc_1(sK3,sK3) != X1
    | k2_zfmisc_1(sK3,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_1065,plain,
    ( X0 != k2_zfmisc_1(sK3,sK3)
    | k2_zfmisc_1(sK3,sK3) = X0
    | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1267,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK3,sK3)
    | k2_zfmisc_1(sK3,sK3) = k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_2420,plain,
    ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))) != k2_zfmisc_1(sK3,sK3)
    | k2_zfmisc_1(sK3,sK3) = k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3)))
    | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_2290,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k1_wellord2(sK3)))
    | ~ r1_tarski(k2_relat_1(k1_wellord2(sK3)),X0)
    | k2_relat_1(k1_wellord2(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2291,plain,
    ( k2_relat_1(k1_wellord2(sK3)) = X0
    | r1_tarski(X0,k2_relat_1(k1_wellord2(sK3))) != iProver_top
    | r1_tarski(k2_relat_1(k1_wellord2(sK3)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2290])).

cnf(c_2293,plain,
    ( k2_relat_1(k1_wellord2(sK3)) = sK3
    | r1_tarski(k2_relat_1(k1_wellord2(sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k2_relat_1(k1_wellord2(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2291])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_965,plain,
    ( r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))))
    | ~ v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_438,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_845,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))
    | k2_zfmisc_1(sK3,sK3) != X1
    | k1_wellord2(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_862,plain,
    ( ~ r1_tarski(k1_wellord2(sK3),X0)
    | r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))
    | k2_zfmisc_1(sK3,sK3) != X0
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_888,plain,
    ( ~ r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))))
    | r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))
    | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3)))
    | k1_wellord2(sK3) != k1_wellord2(sK3) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_449,plain,
    ( X0 != X1
    | k1_wellord2(X0) = k1_wellord2(X1) ),
    theory(equality)).

cnf(c_463,plain,
    ( k1_wellord2(sK3) = k1_wellord2(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_459,plain,
    ( k2_zfmisc_1(sK3,sK3) = k2_zfmisc_1(sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_94,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_90,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_29,plain,
    ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_28,plain,
    ( v1_relat_1(k1_wellord2(sK3)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9610,c_9607,c_5149,c_2737,c_2484,c_2420,c_2293,c_965,c_888,c_463,c_459,c_94,c_90,c_29,c_28,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 4.05/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/0.99  
% 4.05/0.99  ------  iProver source info
% 4.05/0.99  
% 4.05/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.05/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/0.99  git: non_committed_changes: false
% 4.05/0.99  git: last_make_outside_of_git: false
% 4.05/0.99  
% 4.05/0.99  ------ 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options
% 4.05/0.99  
% 4.05/0.99  --out_options                           all
% 4.05/0.99  --tptp_safe_out                         true
% 4.05/0.99  --problem_path                          ""
% 4.05/0.99  --include_path                          ""
% 4.05/0.99  --clausifier                            res/vclausify_rel
% 4.05/0.99  --clausifier_options                    ""
% 4.05/0.99  --stdin                                 false
% 4.05/0.99  --stats_out                             all
% 4.05/0.99  
% 4.05/0.99  ------ General Options
% 4.05/0.99  
% 4.05/0.99  --fof                                   false
% 4.05/0.99  --time_out_real                         305.
% 4.05/0.99  --time_out_virtual                      -1.
% 4.05/0.99  --symbol_type_check                     false
% 4.05/0.99  --clausify_out                          false
% 4.05/0.99  --sig_cnt_out                           false
% 4.05/0.99  --trig_cnt_out                          false
% 4.05/0.99  --trig_cnt_out_tolerance                1.
% 4.05/0.99  --trig_cnt_out_sk_spl                   false
% 4.05/0.99  --abstr_cl_out                          false
% 4.05/0.99  
% 4.05/0.99  ------ Global Options
% 4.05/0.99  
% 4.05/0.99  --schedule                              default
% 4.05/0.99  --add_important_lit                     false
% 4.05/0.99  --prop_solver_per_cl                    1000
% 4.05/0.99  --min_unsat_core                        false
% 4.05/0.99  --soft_assumptions                      false
% 4.05/0.99  --soft_lemma_size                       3
% 4.05/0.99  --prop_impl_unit_size                   0
% 4.05/0.99  --prop_impl_unit                        []
% 4.05/0.99  --share_sel_clauses                     true
% 4.05/0.99  --reset_solvers                         false
% 4.05/0.99  --bc_imp_inh                            [conj_cone]
% 4.05/0.99  --conj_cone_tolerance                   3.
% 4.05/0.99  --extra_neg_conj                        none
% 4.05/0.99  --large_theory_mode                     true
% 4.05/0.99  --prolific_symb_bound                   200
% 4.05/0.99  --lt_threshold                          2000
% 4.05/0.99  --clause_weak_htbl                      true
% 4.05/0.99  --gc_record_bc_elim                     false
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing Options
% 4.05/0.99  
% 4.05/0.99  --preprocessing_flag                    true
% 4.05/0.99  --time_out_prep_mult                    0.1
% 4.05/0.99  --splitting_mode                        input
% 4.05/0.99  --splitting_grd                         true
% 4.05/0.99  --splitting_cvd                         false
% 4.05/0.99  --splitting_cvd_svl                     false
% 4.05/0.99  --splitting_nvd                         32
% 4.05/0.99  --sub_typing                            true
% 4.05/0.99  --prep_gs_sim                           true
% 4.05/0.99  --prep_unflatten                        true
% 4.05/0.99  --prep_res_sim                          true
% 4.05/0.99  --prep_upred                            true
% 4.05/0.99  --prep_sem_filter                       exhaustive
% 4.05/0.99  --prep_sem_filter_out                   false
% 4.05/0.99  --pred_elim                             true
% 4.05/0.99  --res_sim_input                         true
% 4.05/0.99  --eq_ax_congr_red                       true
% 4.05/0.99  --pure_diseq_elim                       true
% 4.05/0.99  --brand_transform                       false
% 4.05/0.99  --non_eq_to_eq                          false
% 4.05/0.99  --prep_def_merge                        true
% 4.05/0.99  --prep_def_merge_prop_impl              false
% 4.05/0.99  --prep_def_merge_mbd                    true
% 4.05/0.99  --prep_def_merge_tr_red                 false
% 4.05/0.99  --prep_def_merge_tr_cl                  false
% 4.05/0.99  --smt_preprocessing                     true
% 4.05/0.99  --smt_ac_axioms                         fast
% 4.05/0.99  --preprocessed_out                      false
% 4.05/0.99  --preprocessed_stats                    false
% 4.05/0.99  
% 4.05/0.99  ------ Abstraction refinement Options
% 4.05/0.99  
% 4.05/0.99  --abstr_ref                             []
% 4.05/0.99  --abstr_ref_prep                        false
% 4.05/0.99  --abstr_ref_until_sat                   false
% 4.05/0.99  --abstr_ref_sig_restrict                funpre
% 4.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.99  --abstr_ref_under                       []
% 4.05/0.99  
% 4.05/0.99  ------ SAT Options
% 4.05/0.99  
% 4.05/0.99  --sat_mode                              false
% 4.05/0.99  --sat_fm_restart_options                ""
% 4.05/0.99  --sat_gr_def                            false
% 4.05/0.99  --sat_epr_types                         true
% 4.05/0.99  --sat_non_cyclic_types                  false
% 4.05/0.99  --sat_finite_models                     false
% 4.05/0.99  --sat_fm_lemmas                         false
% 4.05/0.99  --sat_fm_prep                           false
% 4.05/0.99  --sat_fm_uc_incr                        true
% 4.05/0.99  --sat_out_model                         small
% 4.05/0.99  --sat_out_clauses                       false
% 4.05/0.99  
% 4.05/0.99  ------ QBF Options
% 4.05/0.99  
% 4.05/0.99  --qbf_mode                              false
% 4.05/0.99  --qbf_elim_univ                         false
% 4.05/0.99  --qbf_dom_inst                          none
% 4.05/0.99  --qbf_dom_pre_inst                      false
% 4.05/0.99  --qbf_sk_in                             false
% 4.05/0.99  --qbf_pred_elim                         true
% 4.05/0.99  --qbf_split                             512
% 4.05/0.99  
% 4.05/0.99  ------ BMC1 Options
% 4.05/0.99  
% 4.05/0.99  --bmc1_incremental                      false
% 4.05/0.99  --bmc1_axioms                           reachable_all
% 4.05/0.99  --bmc1_min_bound                        0
% 4.05/0.99  --bmc1_max_bound                        -1
% 4.05/0.99  --bmc1_max_bound_default                -1
% 4.05/0.99  --bmc1_symbol_reachability              true
% 4.05/0.99  --bmc1_property_lemmas                  false
% 4.05/0.99  --bmc1_k_induction                      false
% 4.05/0.99  --bmc1_non_equiv_states                 false
% 4.05/0.99  --bmc1_deadlock                         false
% 4.05/0.99  --bmc1_ucm                              false
% 4.05/0.99  --bmc1_add_unsat_core                   none
% 4.05/0.99  --bmc1_unsat_core_children              false
% 4.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.99  --bmc1_out_stat                         full
% 4.05/0.99  --bmc1_ground_init                      false
% 4.05/0.99  --bmc1_pre_inst_next_state              false
% 4.05/0.99  --bmc1_pre_inst_state                   false
% 4.05/0.99  --bmc1_pre_inst_reach_state             false
% 4.05/0.99  --bmc1_out_unsat_core                   false
% 4.05/0.99  --bmc1_aig_witness_out                  false
% 4.05/0.99  --bmc1_verbose                          false
% 4.05/0.99  --bmc1_dump_clauses_tptp                false
% 4.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.99  --bmc1_dump_file                        -
% 4.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.99  --bmc1_ucm_extend_mode                  1
% 4.05/0.99  --bmc1_ucm_init_mode                    2
% 4.05/0.99  --bmc1_ucm_cone_mode                    none
% 4.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.99  --bmc1_ucm_relax_model                  4
% 4.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.99  --bmc1_ucm_layered_model                none
% 4.05/0.99  --bmc1_ucm_max_lemma_size               10
% 4.05/0.99  
% 4.05/0.99  ------ AIG Options
% 4.05/0.99  
% 4.05/0.99  --aig_mode                              false
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation Options
% 4.05/0.99  
% 4.05/0.99  --instantiation_flag                    true
% 4.05/0.99  --inst_sos_flag                         true
% 4.05/0.99  --inst_sos_phase                        true
% 4.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel_side                     num_symb
% 4.05/0.99  --inst_solver_per_active                1400
% 4.05/0.99  --inst_solver_calls_frac                1.
% 4.05/0.99  --inst_passive_queue_type               priority_queues
% 4.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.99  --inst_passive_queues_freq              [25;2]
% 4.05/0.99  --inst_dismatching                      true
% 4.05/0.99  --inst_eager_unprocessed_to_passive     true
% 4.05/0.99  --inst_prop_sim_given                   true
% 4.05/0.99  --inst_prop_sim_new                     false
% 4.05/0.99  --inst_subs_new                         false
% 4.05/0.99  --inst_eq_res_simp                      false
% 4.05/0.99  --inst_subs_given                       false
% 4.05/0.99  --inst_orphan_elimination               true
% 4.05/0.99  --inst_learning_loop_flag               true
% 4.05/0.99  --inst_learning_start                   3000
% 4.05/0.99  --inst_learning_factor                  2
% 4.05/0.99  --inst_start_prop_sim_after_learn       3
% 4.05/0.99  --inst_sel_renew                        solver
% 4.05/0.99  --inst_lit_activity_flag                true
% 4.05/0.99  --inst_restr_to_given                   false
% 4.05/0.99  --inst_activity_threshold               500
% 4.05/0.99  --inst_out_proof                        true
% 4.05/0.99  
% 4.05/0.99  ------ Resolution Options
% 4.05/0.99  
% 4.05/0.99  --resolution_flag                       true
% 4.05/0.99  --res_lit_sel                           adaptive
% 4.05/0.99  --res_lit_sel_side                      none
% 4.05/0.99  --res_ordering                          kbo
% 4.05/0.99  --res_to_prop_solver                    active
% 4.05/0.99  --res_prop_simpl_new                    false
% 4.05/0.99  --res_prop_simpl_given                  true
% 4.05/0.99  --res_passive_queue_type                priority_queues
% 4.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.99  --res_passive_queues_freq               [15;5]
% 4.05/0.99  --res_forward_subs                      full
% 4.05/0.99  --res_backward_subs                     full
% 4.05/0.99  --res_forward_subs_resolution           true
% 4.05/0.99  --res_backward_subs_resolution          true
% 4.05/0.99  --res_orphan_elimination                true
% 4.05/0.99  --res_time_limit                        2.
% 4.05/0.99  --res_out_proof                         true
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Options
% 4.05/0.99  
% 4.05/0.99  --superposition_flag                    true
% 4.05/0.99  --sup_passive_queue_type                priority_queues
% 4.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.99  --demod_completeness_check              fast
% 4.05/0.99  --demod_use_ground                      true
% 4.05/0.99  --sup_to_prop_solver                    passive
% 4.05/0.99  --sup_prop_simpl_new                    true
% 4.05/0.99  --sup_prop_simpl_given                  true
% 4.05/0.99  --sup_fun_splitting                     true
% 4.05/0.99  --sup_smt_interval                      50000
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Simplification Setup
% 4.05/0.99  
% 4.05/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_immed_triv                        [TrivRules]
% 4.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_bw_main                     []
% 4.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_input_bw                          []
% 4.05/0.99  
% 4.05/0.99  ------ Combination Options
% 4.05/0.99  
% 4.05/0.99  --comb_res_mult                         3
% 4.05/0.99  --comb_sup_mult                         2
% 4.05/0.99  --comb_inst_mult                        10
% 4.05/0.99  
% 4.05/0.99  ------ Debug Options
% 4.05/0.99  
% 4.05/0.99  --dbg_backtrace                         false
% 4.05/0.99  --dbg_dump_prop_clauses                 false
% 4.05/0.99  --dbg_dump_prop_clauses_file            -
% 4.05/0.99  --dbg_out_stat                          false
% 4.05/0.99  ------ Parsing...
% 4.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/0.99  ------ Proving...
% 4.05/0.99  ------ Problem Properties 
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  clauses                                 25
% 4.05/0.99  conjectures                             1
% 4.05/0.99  EPR                                     2
% 4.05/0.99  Horn                                    21
% 4.05/0.99  unary                                   8
% 4.05/0.99  binary                                  5
% 4.05/0.99  lits                                    62
% 4.05/0.99  lits eq                                 12
% 4.05/0.99  fd_pure                                 0
% 4.05/0.99  fd_pseudo                               0
% 4.05/0.99  fd_cond                                 0
% 4.05/0.99  fd_pseudo_cond                          1
% 4.05/0.99  AC symbols                              0
% 4.05/0.99  
% 4.05/0.99  ------ Schedule dynamic 5 is on 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  ------ 
% 4.05/0.99  Current options:
% 4.05/0.99  ------ 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options
% 4.05/0.99  
% 4.05/0.99  --out_options                           all
% 4.05/0.99  --tptp_safe_out                         true
% 4.05/0.99  --problem_path                          ""
% 4.05/0.99  --include_path                          ""
% 4.05/0.99  --clausifier                            res/vclausify_rel
% 4.05/0.99  --clausifier_options                    ""
% 4.05/0.99  --stdin                                 false
% 4.05/0.99  --stats_out                             all
% 4.05/0.99  
% 4.05/0.99  ------ General Options
% 4.05/0.99  
% 4.05/0.99  --fof                                   false
% 4.05/0.99  --time_out_real                         305.
% 4.05/0.99  --time_out_virtual                      -1.
% 4.05/0.99  --symbol_type_check                     false
% 4.05/0.99  --clausify_out                          false
% 4.05/0.99  --sig_cnt_out                           false
% 4.05/0.99  --trig_cnt_out                          false
% 4.05/0.99  --trig_cnt_out_tolerance                1.
% 4.05/0.99  --trig_cnt_out_sk_spl                   false
% 4.05/0.99  --abstr_cl_out                          false
% 4.05/0.99  
% 4.05/0.99  ------ Global Options
% 4.05/0.99  
% 4.05/0.99  --schedule                              default
% 4.05/0.99  --add_important_lit                     false
% 4.05/0.99  --prop_solver_per_cl                    1000
% 4.05/0.99  --min_unsat_core                        false
% 4.05/0.99  --soft_assumptions                      false
% 4.05/0.99  --soft_lemma_size                       3
% 4.05/0.99  --prop_impl_unit_size                   0
% 4.05/0.99  --prop_impl_unit                        []
% 4.05/0.99  --share_sel_clauses                     true
% 4.05/0.99  --reset_solvers                         false
% 4.05/0.99  --bc_imp_inh                            [conj_cone]
% 4.05/0.99  --conj_cone_tolerance                   3.
% 4.05/0.99  --extra_neg_conj                        none
% 4.05/0.99  --large_theory_mode                     true
% 4.05/0.99  --prolific_symb_bound                   200
% 4.05/1.00  --lt_threshold                          2000
% 4.05/1.00  --clause_weak_htbl                      true
% 4.05/1.00  --gc_record_bc_elim                     false
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing Options
% 4.05/1.00  
% 4.05/1.00  --preprocessing_flag                    true
% 4.05/1.00  --time_out_prep_mult                    0.1
% 4.05/1.00  --splitting_mode                        input
% 4.05/1.00  --splitting_grd                         true
% 4.05/1.00  --splitting_cvd                         false
% 4.05/1.00  --splitting_cvd_svl                     false
% 4.05/1.00  --splitting_nvd                         32
% 4.05/1.00  --sub_typing                            true
% 4.05/1.00  --prep_gs_sim                           true
% 4.05/1.00  --prep_unflatten                        true
% 4.05/1.00  --prep_res_sim                          true
% 4.05/1.00  --prep_upred                            true
% 4.05/1.00  --prep_sem_filter                       exhaustive
% 4.05/1.00  --prep_sem_filter_out                   false
% 4.05/1.00  --pred_elim                             true
% 4.05/1.00  --res_sim_input                         true
% 4.05/1.00  --eq_ax_congr_red                       true
% 4.05/1.00  --pure_diseq_elim                       true
% 4.05/1.00  --brand_transform                       false
% 4.05/1.00  --non_eq_to_eq                          false
% 4.05/1.00  --prep_def_merge                        true
% 4.05/1.00  --prep_def_merge_prop_impl              false
% 4.05/1.00  --prep_def_merge_mbd                    true
% 4.05/1.00  --prep_def_merge_tr_red                 false
% 4.05/1.00  --prep_def_merge_tr_cl                  false
% 4.05/1.00  --smt_preprocessing                     true
% 4.05/1.00  --smt_ac_axioms                         fast
% 4.05/1.00  --preprocessed_out                      false
% 4.05/1.00  --preprocessed_stats                    false
% 4.05/1.00  
% 4.05/1.00  ------ Abstraction refinement Options
% 4.05/1.00  
% 4.05/1.00  --abstr_ref                             []
% 4.05/1.00  --abstr_ref_prep                        false
% 4.05/1.00  --abstr_ref_until_sat                   false
% 4.05/1.00  --abstr_ref_sig_restrict                funpre
% 4.05/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/1.00  --abstr_ref_under                       []
% 4.05/1.00  
% 4.05/1.00  ------ SAT Options
% 4.05/1.00  
% 4.05/1.00  --sat_mode                              false
% 4.05/1.00  --sat_fm_restart_options                ""
% 4.05/1.00  --sat_gr_def                            false
% 4.05/1.00  --sat_epr_types                         true
% 4.05/1.00  --sat_non_cyclic_types                  false
% 4.05/1.00  --sat_finite_models                     false
% 4.05/1.00  --sat_fm_lemmas                         false
% 4.05/1.00  --sat_fm_prep                           false
% 4.05/1.00  --sat_fm_uc_incr                        true
% 4.05/1.00  --sat_out_model                         small
% 4.05/1.00  --sat_out_clauses                       false
% 4.05/1.00  
% 4.05/1.00  ------ QBF Options
% 4.05/1.00  
% 4.05/1.00  --qbf_mode                              false
% 4.05/1.00  --qbf_elim_univ                         false
% 4.05/1.00  --qbf_dom_inst                          none
% 4.05/1.00  --qbf_dom_pre_inst                      false
% 4.05/1.00  --qbf_sk_in                             false
% 4.05/1.00  --qbf_pred_elim                         true
% 4.05/1.00  --qbf_split                             512
% 4.05/1.00  
% 4.05/1.00  ------ BMC1 Options
% 4.05/1.00  
% 4.05/1.00  --bmc1_incremental                      false
% 4.05/1.00  --bmc1_axioms                           reachable_all
% 4.05/1.00  --bmc1_min_bound                        0
% 4.05/1.00  --bmc1_max_bound                        -1
% 4.05/1.00  --bmc1_max_bound_default                -1
% 4.05/1.00  --bmc1_symbol_reachability              true
% 4.05/1.00  --bmc1_property_lemmas                  false
% 4.05/1.00  --bmc1_k_induction                      false
% 4.05/1.00  --bmc1_non_equiv_states                 false
% 4.05/1.00  --bmc1_deadlock                         false
% 4.05/1.00  --bmc1_ucm                              false
% 4.05/1.00  --bmc1_add_unsat_core                   none
% 4.05/1.00  --bmc1_unsat_core_children              false
% 4.05/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/1.00  --bmc1_out_stat                         full
% 4.05/1.00  --bmc1_ground_init                      false
% 4.05/1.00  --bmc1_pre_inst_next_state              false
% 4.05/1.00  --bmc1_pre_inst_state                   false
% 4.05/1.00  --bmc1_pre_inst_reach_state             false
% 4.05/1.00  --bmc1_out_unsat_core                   false
% 4.05/1.00  --bmc1_aig_witness_out                  false
% 4.05/1.00  --bmc1_verbose                          false
% 4.05/1.00  --bmc1_dump_clauses_tptp                false
% 4.05/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.05/1.00  --bmc1_dump_file                        -
% 4.05/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.05/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.05/1.00  --bmc1_ucm_extend_mode                  1
% 4.05/1.00  --bmc1_ucm_init_mode                    2
% 4.05/1.00  --bmc1_ucm_cone_mode                    none
% 4.05/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.05/1.00  --bmc1_ucm_relax_model                  4
% 4.05/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.05/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/1.00  --bmc1_ucm_layered_model                none
% 4.05/1.00  --bmc1_ucm_max_lemma_size               10
% 4.05/1.00  
% 4.05/1.00  ------ AIG Options
% 4.05/1.00  
% 4.05/1.00  --aig_mode                              false
% 4.05/1.00  
% 4.05/1.00  ------ Instantiation Options
% 4.05/1.00  
% 4.05/1.00  --instantiation_flag                    true
% 4.05/1.00  --inst_sos_flag                         true
% 4.05/1.00  --inst_sos_phase                        true
% 4.05/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/1.00  --inst_lit_sel_side                     none
% 4.05/1.00  --inst_solver_per_active                1400
% 4.05/1.00  --inst_solver_calls_frac                1.
% 4.05/1.00  --inst_passive_queue_type               priority_queues
% 4.05/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/1.00  --inst_passive_queues_freq              [25;2]
% 4.05/1.00  --inst_dismatching                      true
% 4.05/1.00  --inst_eager_unprocessed_to_passive     true
% 4.05/1.00  --inst_prop_sim_given                   true
% 4.05/1.00  --inst_prop_sim_new                     false
% 4.05/1.00  --inst_subs_new                         false
% 4.05/1.00  --inst_eq_res_simp                      false
% 4.05/1.00  --inst_subs_given                       false
% 4.05/1.00  --inst_orphan_elimination               true
% 4.05/1.00  --inst_learning_loop_flag               true
% 4.05/1.00  --inst_learning_start                   3000
% 4.05/1.00  --inst_learning_factor                  2
% 4.05/1.00  --inst_start_prop_sim_after_learn       3
% 4.05/1.00  --inst_sel_renew                        solver
% 4.05/1.00  --inst_lit_activity_flag                true
% 4.05/1.00  --inst_restr_to_given                   false
% 4.05/1.00  --inst_activity_threshold               500
% 4.05/1.00  --inst_out_proof                        true
% 4.05/1.00  
% 4.05/1.00  ------ Resolution Options
% 4.05/1.00  
% 4.05/1.00  --resolution_flag                       false
% 4.05/1.00  --res_lit_sel                           adaptive
% 4.05/1.00  --res_lit_sel_side                      none
% 4.05/1.00  --res_ordering                          kbo
% 4.05/1.00  --res_to_prop_solver                    active
% 4.05/1.00  --res_prop_simpl_new                    false
% 4.05/1.00  --res_prop_simpl_given                  true
% 4.05/1.00  --res_passive_queue_type                priority_queues
% 4.05/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/1.00  --res_passive_queues_freq               [15;5]
% 4.05/1.00  --res_forward_subs                      full
% 4.05/1.00  --res_backward_subs                     full
% 4.05/1.00  --res_forward_subs_resolution           true
% 4.05/1.00  --res_backward_subs_resolution          true
% 4.05/1.00  --res_orphan_elimination                true
% 4.05/1.00  --res_time_limit                        2.
% 4.05/1.00  --res_out_proof                         true
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Options
% 4.05/1.00  
% 4.05/1.00  --superposition_flag                    true
% 4.05/1.00  --sup_passive_queue_type                priority_queues
% 4.05/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.05/1.00  --demod_completeness_check              fast
% 4.05/1.00  --demod_use_ground                      true
% 4.05/1.00  --sup_to_prop_solver                    passive
% 4.05/1.00  --sup_prop_simpl_new                    true
% 4.05/1.00  --sup_prop_simpl_given                  true
% 4.05/1.00  --sup_fun_splitting                     true
% 4.05/1.00  --sup_smt_interval                      50000
% 4.05/1.00  
% 4.05/1.00  ------ Superposition Simplification Setup
% 4.05/1.00  
% 4.05/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/1.00  --sup_immed_triv                        [TrivRules]
% 4.05/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_immed_bw_main                     []
% 4.05/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/1.00  --sup_input_bw                          []
% 4.05/1.00  
% 4.05/1.00  ------ Combination Options
% 4.05/1.00  
% 4.05/1.00  --comb_res_mult                         3
% 4.05/1.00  --comb_sup_mult                         2
% 4.05/1.00  --comb_inst_mult                        10
% 4.05/1.00  
% 4.05/1.00  ------ Debug Options
% 4.05/1.00  
% 4.05/1.00  --dbg_backtrace                         false
% 4.05/1.00  --dbg_dump_prop_clauses                 false
% 4.05/1.00  --dbg_dump_prop_clauses_file            -
% 4.05/1.00  --dbg_out_stat                          false
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS status Theorem for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  fof(f8,axiom,(
% 4.05/1.00    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f23,plain,(
% 4.05/1.00    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f8])).
% 4.05/1.00  
% 4.05/1.00  fof(f24,plain,(
% 4.05/1.00    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(flattening,[],[f23])).
% 4.05/1.00  
% 4.05/1.00  fof(f34,plain,(
% 4.05/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f35,plain,(
% 4.05/1.00    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1) & r2_hidden(sK0(X0,X1),X0)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f34])).
% 4.05/1.00  
% 4.05/1.00  fof(f54,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | r2_hidden(sK0(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f35])).
% 4.05/1.00  
% 4.05/1.00  fof(f1,axiom,(
% 4.05/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f32,plain,(
% 4.05/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.05/1.00    inference(nnf_transformation,[],[f1])).
% 4.05/1.00  
% 4.05/1.00  fof(f33,plain,(
% 4.05/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.05/1.00    inference(flattening,[],[f32])).
% 4.05/1.00  
% 4.05/1.00  fof(f43,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.05/1.00    inference(cnf_transformation,[],[f33])).
% 4.05/1.00  
% 4.05/1.00  fof(f70,plain,(
% 4.05/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.05/1.00    inference(equality_resolution,[],[f43])).
% 4.05/1.00  
% 4.05/1.00  fof(f13,axiom,(
% 4.05/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f29,plain,(
% 4.05/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f13])).
% 4.05/1.00  
% 4.05/1.00  fof(f30,plain,(
% 4.05/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(flattening,[],[f29])).
% 4.05/1.00  
% 4.05/1.00  fof(f36,plain,(
% 4.05/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(nnf_transformation,[],[f30])).
% 4.05/1.00  
% 4.05/1.00  fof(f37,plain,(
% 4.05/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(flattening,[],[f36])).
% 4.05/1.00  
% 4.05/1.00  fof(f38,plain,(
% 4.05/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(rectify,[],[f37])).
% 4.05/1.00  
% 4.05/1.00  fof(f39,plain,(
% 4.05/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f40,plain,(
% 4.05/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r1_tarski(sK1(X0,X1),sK2(X0,X1)) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f39])).
% 4.05/1.00  
% 4.05/1.00  fof(f62,plain,(
% 4.05/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f40])).
% 4.05/1.00  
% 4.05/1.00  fof(f75,plain,(
% 4.05/1.00    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 4.05/1.00    inference(equality_resolution,[],[f62])).
% 4.05/1.00  
% 4.05/1.00  fof(f55,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1) | ~v1_relat_1(X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f35])).
% 4.05/1.00  
% 4.05/1.00  fof(f14,axiom,(
% 4.05/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f67,plain,(
% 4.05/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f14])).
% 4.05/1.00  
% 4.05/1.00  fof(f7,axiom,(
% 4.05/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f52,plain,(
% 4.05/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.05/1.00    inference(cnf_transformation,[],[f7])).
% 4.05/1.00  
% 4.05/1.00  fof(f6,axiom,(
% 4.05/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f21,plain,(
% 4.05/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f6])).
% 4.05/1.00  
% 4.05/1.00  fof(f22,plain,(
% 4.05/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.05/1.00    inference(flattening,[],[f21])).
% 4.05/1.00  
% 4.05/1.00  fof(f50,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f22])).
% 4.05/1.00  
% 4.05/1.00  fof(f10,axiom,(
% 4.05/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f17,plain,(
% 4.05/1.00    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 4.05/1.00    inference(pure_predicate_removal,[],[f10])).
% 4.05/1.00  
% 4.05/1.00  fof(f57,plain,(
% 4.05/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f17])).
% 4.05/1.00  
% 4.05/1.00  fof(f53,plain,(
% 4.05/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.05/1.00    inference(cnf_transformation,[],[f7])).
% 4.05/1.00  
% 4.05/1.00  fof(f51,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f22])).
% 4.05/1.00  
% 4.05/1.00  fof(f3,axiom,(
% 4.05/1.00    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f18,plain,(
% 4.05/1.00    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f3])).
% 4.05/1.00  
% 4.05/1.00  fof(f47,plain,(
% 4.05/1.00    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f18])).
% 4.05/1.00  
% 4.05/1.00  fof(f60,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f40])).
% 4.05/1.00  
% 4.05/1.00  fof(f77,plain,(
% 4.05/1.00    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 4.05/1.00    inference(equality_resolution,[],[f60])).
% 4.05/1.00  
% 4.05/1.00  fof(f2,axiom,(
% 4.05/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f46,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f2])).
% 4.05/1.00  
% 4.05/1.00  fof(f9,axiom,(
% 4.05/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f25,plain,(
% 4.05/1.00    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f9])).
% 4.05/1.00  
% 4.05/1.00  fof(f26,plain,(
% 4.05/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(flattening,[],[f25])).
% 4.05/1.00  
% 4.05/1.00  fof(f56,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f26])).
% 4.05/1.00  
% 4.05/1.00  fof(f11,axiom,(
% 4.05/1.00    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f27,plain,(
% 4.05/1.00    ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f11])).
% 4.05/1.00  
% 4.05/1.00  fof(f58,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  fof(f12,axiom,(
% 4.05/1.00    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f28,plain,(
% 4.05/1.00    ! [X0] : (k2_wellord1(X0,k3_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f12])).
% 4.05/1.00  
% 4.05/1.00  fof(f59,plain,(
% 4.05/1.00    ( ! [X0] : (k2_wellord1(X0,k3_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f28])).
% 4.05/1.00  
% 4.05/1.00  fof(f4,axiom,(
% 4.05/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f19,plain,(
% 4.05/1.00    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 4.05/1.00    inference(ennf_transformation,[],[f4])).
% 4.05/1.00  
% 4.05/1.00  fof(f48,plain,(
% 4.05/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f19])).
% 4.05/1.00  
% 4.05/1.00  fof(f45,plain,(
% 4.05/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f33])).
% 4.05/1.00  
% 4.05/1.00  fof(f5,axiom,(
% 4.05/1.00    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f20,plain,(
% 4.05/1.00    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f5])).
% 4.05/1.00  
% 4.05/1.00  fof(f49,plain,(
% 4.05/1.00    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f20])).
% 4.05/1.00  
% 4.05/1.00  fof(f15,conjecture,(
% 4.05/1.00    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 4.05/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f16,negated_conjecture,(
% 4.05/1.00    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 4.05/1.00    inference(negated_conjecture,[],[f15])).
% 4.05/1.00  
% 4.05/1.00  fof(f31,plain,(
% 4.05/1.00    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f16])).
% 4.05/1.00  
% 4.05/1.00  fof(f41,plain,(
% 4.05/1.00    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f42,plain,(
% 4.05/1.00    ~r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f41])).
% 4.05/1.00  
% 4.05/1.00  fof(f68,plain,(
% 4.05/1.00    ~r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))),
% 4.05/1.00    inference(cnf_transformation,[],[f42])).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12,plain,
% 4.05/1.00      ( r2_hidden(sK0(X0,X1),X0)
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1)
% 4.05/1.00      | ~ v1_relat_1(X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f54]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_813,plain,
% 4.05/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) = iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2,plain,
% 4.05/1.00      ( r1_tarski(X0,X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f70]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_821,plain,
% 4.05/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_21,plain,
% 4.05/1.00      ( ~ r2_hidden(X0,X1)
% 4.05/1.00      | ~ r2_hidden(X2,X1)
% 4.05/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1))
% 4.05/1.00      | ~ r1_tarski(X2,X0)
% 4.05/1.00      | ~ v1_relat_1(k1_wellord2(X1)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_804,plain,
% 4.05/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.05/1.00      | r2_hidden(X2,X1) != iProver_top
% 4.05/1.00      | r2_hidden(k4_tarski(X2,X0),k1_wellord2(X1)) = iProver_top
% 4.05/1.00      | r1_tarski(X2,X0) != iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11,plain,
% 4.05/1.00      ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1)
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1)
% 4.05/1.00      | ~ v1_relat_1(X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f55]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_814,plain,
% 4.05/1.00      ( r2_hidden(k4_tarski(sK0(X0,X1),sK0(X0,X1)),X1) != iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) = iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_3248,plain,
% 4.05/1.00      ( r2_hidden(sK0(X0,k1_wellord2(X1)),X1) != iProver_top
% 4.05/1.00      | r1_tarski(sK0(X0,k1_wellord2(X1)),sK0(X0,k1_wellord2(X1))) != iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_804,c_814]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9302,plain,
% 4.05/1.00      ( r2_hidden(sK0(X0,k1_wellord2(X1)),X1) != iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(X1)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_821,c_3248]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9587,plain,
% 4.05/1.00      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_813,c_9302]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_24,plain,
% 4.05/1.00      ( v1_relat_1(k1_wellord2(X0)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_27,plain,
% 4.05/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9592,plain,
% 4.05/1.00      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) = iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_9587,c_27]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10,plain,
% 4.05/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f52]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8,plain,
% 4.05/1.00      ( ~ r1_tarski(X0,X1)
% 4.05/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 4.05/1.00      | ~ v1_relat_1(X0)
% 4.05/1.00      | ~ v1_relat_1(X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f50]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_815,plain,
% 4.05/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.05/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 4.05/1.00      | v1_relat_1(X0) != iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4855,plain,
% 4.05/1.00      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top
% 4.05/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10,c_815]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_14,plain,
% 4.05/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_57,plain,
% 4.05/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4935,plain,
% 4.05/1.00      ( v1_relat_1(X1) != iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 4.05/1.00      | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_4855,c_57]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4936,plain,
% 4.05/1.00      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_4935]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9601,plain,
% 4.05/1.00      ( r1_tarski(X0,k1_relat_1(k1_wellord2(X0))) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9592,c_4936]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9610,plain,
% 4.05/1.00      ( r1_tarski(sK3,k1_relat_1(k1_wellord2(sK3))) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_9601]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9,plain,
% 4.05/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f53]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_7,plain,
% 4.05/1.00      ( ~ r1_tarski(X0,X1)
% 4.05/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 4.05/1.00      | ~ v1_relat_1(X0)
% 4.05/1.00      | ~ v1_relat_1(X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_816,plain,
% 4.05/1.00      ( r1_tarski(X0,X1) != iProver_top
% 4.05/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 4.05/1.00      | v1_relat_1(X0) != iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4878,plain,
% 4.05/1.00      ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top
% 4.05/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9,c_816]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5738,plain,
% 4.05/1.00      ( v1_relat_1(X1) != iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 4.05/1.00      | r1_tarski(X0,k2_relat_1(X1)) = iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_4878,c_57]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5739,plain,
% 4.05/1.00      ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
% 4.05/1.00      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_5738]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9600,plain,
% 4.05/1.00      ( r1_tarski(X0,k2_relat_1(k1_wellord2(X0))) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9592,c_5739]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9607,plain,
% 4.05/1.00      ( r1_tarski(sK3,k2_relat_1(k1_wellord2(sK3))) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_9600]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_802,plain,
% 4.05/1.00      ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4,plain,
% 4.05/1.00      ( ~ v1_relat_1(X0)
% 4.05/1.00      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f47]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_819,plain,
% 4.05/1.00      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 4.05/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1424,plain,
% 4.05/1.00      ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = k3_relat_1(k1_wellord2(X0)) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_802,c_819]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_23,plain,
% 4.05/1.00      ( ~ v1_relat_1(k1_wellord2(X0))
% 4.05/1.00      | k3_relat_1(k1_wellord2(X0)) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_147,plain,
% 4.05/1.00      ( k3_relat_1(k1_wellord2(X0)) = X0 ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_23,c_24]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1425,plain,
% 4.05/1.00      ( k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_1424,c_147]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_3,plain,
% 4.05/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f46]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_820,plain,
% 4.05/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13,plain,
% 4.05/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 4.05/1.00      | ~ v1_relat_1(X0)
% 4.05/1.00      | k7_relat_1(X0,X1) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_812,plain,
% 4.05/1.00      ( k7_relat_1(X0,X1) = X0
% 4.05/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 4.05/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2491,plain,
% 4.05/1.00      ( k7_relat_1(X0,k2_xboole_0(k1_relat_1(X0),X1)) = X0
% 4.05/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_820,c_812]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4359,plain,
% 4.05/1.00      ( k7_relat_1(k1_wellord2(X0),k2_xboole_0(k1_relat_1(k1_wellord2(X0)),X1)) = k1_wellord2(X0) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_802,c_2491]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4995,plain,
% 4.05/1.00      ( k7_relat_1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_1425,c_4359]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_15,plain,
% 4.05/1.00      ( ~ v1_relat_1(X0)
% 4.05/1.00      | k8_relat_1(X1,k7_relat_1(X0,X1)) = k2_wellord1(X0,X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_810,plain,
% 4.05/1.00      ( k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0)
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2019,plain,
% 4.05/1.00      ( k8_relat_1(X0,k7_relat_1(k1_wellord2(X1),X0)) = k2_wellord1(k1_wellord2(X1),X0) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_802,c_810]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5001,plain,
% 4.05/1.00      ( k2_wellord1(k1_wellord2(X0),X0) = k8_relat_1(X0,k1_wellord2(X0)) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_4995,c_2019]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_16,plain,
% 4.05/1.00      ( ~ v1_relat_1(X0) | k2_wellord1(X0,k3_relat_1(X0)) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_809,plain,
% 4.05/1.00      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
% 4.05/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1281,plain,
% 4.05/1.00      ( k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0))) = k1_wellord2(X0) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_802,c_809]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1282,plain,
% 4.05/1.00      ( k2_wellord1(k1_wellord2(X0),X0) = k1_wellord2(X0) ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_1281,c_147]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5002,plain,
% 4.05/1.00      ( k8_relat_1(X0,k1_wellord2(X0)) = k1_wellord2(X0) ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_5001,c_1282]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5,plain,
% 4.05/1.00      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~ v1_relat_1(X1) ),
% 4.05/1.00      inference(cnf_transformation,[],[f48]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_818,plain,
% 4.05/1.00      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
% 4.05/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5147,plain,
% 4.05/1.00      ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_5002,c_818]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5149,plain,
% 4.05/1.00      ( r1_tarski(k2_relat_1(k1_wellord2(sK3)),sK3) = iProver_top
% 4.05/1.00      | v1_relat_1(k1_wellord2(sK3)) != iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_5147]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_445,plain,
% 4.05/1.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 4.05/1.00      theory(equality) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2737,plain,
% 4.05/1.00      ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))) = k2_zfmisc_1(sK3,sK3)
% 4.05/1.00      | k2_relat_1(k1_wellord2(sK3)) != sK3
% 4.05/1.00      | k1_relat_1(k1_wellord2(sK3)) != sK3 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_445]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1841,plain,
% 4.05/1.00      ( r1_tarski(k1_relat_1(k1_wellord2(X0)),X0) = iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_1425,c_820]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_0,plain,
% 4.05/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.05/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_822,plain,
% 4.05/1.00      ( X0 = X1
% 4.05/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.05/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2469,plain,
% 4.05/1.00      ( k1_relat_1(k1_wellord2(X0)) = X0
% 4.05/1.00      | r1_tarski(X0,k1_relat_1(k1_wellord2(X0))) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_1841,c_822]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2484,plain,
% 4.05/1.00      ( k1_relat_1(k1_wellord2(sK3)) = sK3
% 4.05/1.00      | r1_tarski(sK3,k1_relat_1(k1_wellord2(sK3))) != iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_2469]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_437,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_947,plain,
% 4.05/1.00      ( X0 != X1
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) != X1
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) = X0 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_437]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1065,plain,
% 4.05/1.00      ( X0 != k2_zfmisc_1(sK3,sK3)
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) = X0
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(sK3,sK3) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_947]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1267,plain,
% 4.05/1.00      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK3,sK3)
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) = k2_zfmisc_1(X0,X1)
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(sK3,sK3) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_1065]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2420,plain,
% 4.05/1.00      ( k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))) != k2_zfmisc_1(sK3,sK3)
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) = k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3)))
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(sK3,sK3) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_1267]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2290,plain,
% 4.05/1.00      ( ~ r1_tarski(X0,k2_relat_1(k1_wellord2(sK3)))
% 4.05/1.00      | ~ r1_tarski(k2_relat_1(k1_wellord2(sK3)),X0)
% 4.05/1.00      | k2_relat_1(k1_wellord2(sK3)) = X0 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2291,plain,
% 4.05/1.00      ( k2_relat_1(k1_wellord2(sK3)) = X0
% 4.05/1.00      | r1_tarski(X0,k2_relat_1(k1_wellord2(sK3))) != iProver_top
% 4.05/1.00      | r1_tarski(k2_relat_1(k1_wellord2(sK3)),X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_2290]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2293,plain,
% 4.05/1.00      ( k2_relat_1(k1_wellord2(sK3)) = sK3
% 4.05/1.00      | r1_tarski(k2_relat_1(k1_wellord2(sK3)),sK3) != iProver_top
% 4.05/1.00      | r1_tarski(sK3,k2_relat_1(k1_wellord2(sK3))) != iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_2291]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_6,plain,
% 4.05/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 4.05/1.00      | ~ v1_relat_1(X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f49]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_965,plain,
% 4.05/1.00      ( r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))))
% 4.05/1.00      | ~ v1_relat_1(k1_wellord2(sK3)) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_438,plain,
% 4.05/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.05/1.00      theory(equality) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_845,plain,
% 4.05/1.00      ( ~ r1_tarski(X0,X1)
% 4.05/1.00      | r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) != X1
% 4.05/1.00      | k1_wellord2(sK3) != X0 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_438]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_862,plain,
% 4.05/1.00      ( ~ r1_tarski(k1_wellord2(sK3),X0)
% 4.05/1.00      | r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) != X0
% 4.05/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_845]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_888,plain,
% 4.05/1.00      ( ~ r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3))))
% 4.05/1.00      | r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3))
% 4.05/1.00      | k2_zfmisc_1(sK3,sK3) != k2_zfmisc_1(k1_relat_1(k1_wellord2(sK3)),k2_relat_1(k1_wellord2(sK3)))
% 4.05/1.00      | k1_wellord2(sK3) != k1_wellord2(sK3) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_862]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_449,plain,
% 4.05/1.00      ( X0 != X1 | k1_wellord2(X0) = k1_wellord2(X1) ),
% 4.05/1.00      theory(equality) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_463,plain,
% 4.05/1.00      ( k1_wellord2(sK3) = k1_wellord2(sK3) | sK3 != sK3 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_449]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_459,plain,
% 4.05/1.00      ( k2_zfmisc_1(sK3,sK3) = k2_zfmisc_1(sK3,sK3) | sK3 != sK3 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_445]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_94,plain,
% 4.05/1.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_90,plain,
% 4.05/1.00      ( r1_tarski(sK3,sK3) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_29,plain,
% 4.05/1.00      ( v1_relat_1(k1_wellord2(sK3)) = iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_28,plain,
% 4.05/1.00      ( v1_relat_1(k1_wellord2(sK3)) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_25,negated_conjecture,
% 4.05/1.00      ( ~ r1_tarski(k1_wellord2(sK3),k2_zfmisc_1(sK3,sK3)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(contradiction,plain,
% 4.05/1.00      ( $false ),
% 4.05/1.00      inference(minisat,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_9610,c_9607,c_5149,c_2737,c_2484,c_2420,c_2293,c_965,
% 4.05/1.00                 c_888,c_463,c_459,c_94,c_90,c_29,c_28,c_25]) ).
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  ------                               Statistics
% 4.05/1.00  
% 4.05/1.00  ------ General
% 4.05/1.00  
% 4.05/1.00  abstr_ref_over_cycles:                  0
% 4.05/1.00  abstr_ref_under_cycles:                 0
% 4.05/1.00  gc_basic_clause_elim:                   0
% 4.05/1.00  forced_gc_time:                         0
% 4.05/1.00  parsing_time:                           0.01
% 4.05/1.00  unif_index_cands_time:                  0.
% 4.05/1.00  unif_index_add_time:                    0.
% 4.05/1.00  orderings_time:                         0.
% 4.05/1.00  out_proof_time:                         0.013
% 4.05/1.00  total_time:                             0.364
% 4.05/1.00  num_of_symbols:                         49
% 4.05/1.00  num_of_terms:                           15476
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing
% 4.05/1.00  
% 4.05/1.00  num_of_splits:                          0
% 4.05/1.00  num_of_split_atoms:                     0
% 4.05/1.00  num_of_reused_defs:                     0
% 4.05/1.00  num_eq_ax_congr_red:                    27
% 4.05/1.00  num_of_sem_filtered_clauses:            1
% 4.05/1.00  num_of_subtypes:                        0
% 4.05/1.00  monotx_restored_types:                  0
% 4.05/1.00  sat_num_of_epr_types:                   0
% 4.05/1.00  sat_num_of_non_cyclic_types:            0
% 4.05/1.00  sat_guarded_non_collapsed_types:        0
% 4.05/1.00  num_pure_diseq_elim:                    0
% 4.05/1.00  simp_replaced_by:                       0
% 4.05/1.00  res_preprocessed:                       133
% 4.05/1.00  prep_upred:                             0
% 4.05/1.00  prep_unflattend:                        0
% 4.05/1.00  smt_new_axioms:                         0
% 4.05/1.00  pred_elim_cands:                        3
% 4.05/1.00  pred_elim:                              0
% 4.05/1.00  pred_elim_cl:                           0
% 4.05/1.00  pred_elim_cycles:                       2
% 4.05/1.00  merged_defs:                            0
% 4.05/1.00  merged_defs_ncl:                        0
% 4.05/1.00  bin_hyper_res:                          0
% 4.05/1.00  prep_cycles:                            4
% 4.05/1.00  pred_elim_time:                         0.001
% 4.05/1.00  splitting_time:                         0.
% 4.05/1.00  sem_filter_time:                        0.
% 4.05/1.00  monotx_time:                            0.
% 4.05/1.00  subtype_inf_time:                       0.
% 4.05/1.00  
% 4.05/1.00  ------ Problem properties
% 4.05/1.00  
% 4.05/1.00  clauses:                                25
% 4.05/1.00  conjectures:                            1
% 4.05/1.00  epr:                                    2
% 4.05/1.00  horn:                                   21
% 4.05/1.00  ground:                                 1
% 4.05/1.00  unary:                                  8
% 4.05/1.00  binary:                                 5
% 4.05/1.00  lits:                                   62
% 4.05/1.00  lits_eq:                                12
% 4.05/1.00  fd_pure:                                0
% 4.05/1.00  fd_pseudo:                              0
% 4.05/1.00  fd_cond:                                0
% 4.05/1.00  fd_pseudo_cond:                         1
% 4.05/1.00  ac_symbols:                             0
% 4.05/1.00  
% 4.05/1.00  ------ Propositional Solver
% 4.05/1.00  
% 4.05/1.00  prop_solver_calls:                      31
% 4.05/1.00  prop_fast_solver_calls:                 867
% 4.05/1.00  smt_solver_calls:                       0
% 4.05/1.00  smt_fast_solver_calls:                  0
% 4.05/1.00  prop_num_of_clauses:                    4949
% 4.05/1.00  prop_preprocess_simplified:             14135
% 4.05/1.00  prop_fo_subsumed:                       7
% 4.05/1.00  prop_solver_time:                       0.
% 4.05/1.00  smt_solver_time:                        0.
% 4.05/1.00  smt_fast_solver_time:                   0.
% 4.05/1.00  prop_fast_solver_time:                  0.
% 4.05/1.00  prop_unsat_core_time:                   0.
% 4.05/1.00  
% 4.05/1.00  ------ QBF
% 4.05/1.00  
% 4.05/1.00  qbf_q_res:                              0
% 4.05/1.00  qbf_num_tautologies:                    0
% 4.05/1.00  qbf_prep_cycles:                        0
% 4.05/1.00  
% 4.05/1.00  ------ BMC1
% 4.05/1.00  
% 4.05/1.00  bmc1_current_bound:                     -1
% 4.05/1.00  bmc1_last_solved_bound:                 -1
% 4.05/1.00  bmc1_unsat_core_size:                   -1
% 4.05/1.00  bmc1_unsat_core_parents_size:           -1
% 4.05/1.00  bmc1_merge_next_fun:                    0
% 4.05/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.05/1.00  
% 4.05/1.00  ------ Instantiation
% 4.05/1.00  
% 4.05/1.00  inst_num_of_clauses:                    1683
% 4.05/1.00  inst_num_in_passive:                    1009
% 4.05/1.00  inst_num_in_active:                     475
% 4.05/1.00  inst_num_in_unprocessed:                199
% 4.05/1.00  inst_num_of_loops:                      500
% 4.05/1.00  inst_num_of_learning_restarts:          0
% 4.05/1.00  inst_num_moves_active_passive:          23
% 4.05/1.00  inst_lit_activity:                      0
% 4.05/1.00  inst_lit_activity_moves:                0
% 4.05/1.00  inst_num_tautologies:                   0
% 4.05/1.00  inst_num_prop_implied:                  0
% 4.05/1.00  inst_num_existing_simplified:           0
% 4.05/1.00  inst_num_eq_res_simplified:             0
% 4.05/1.00  inst_num_child_elim:                    0
% 4.05/1.00  inst_num_of_dismatching_blockings:      443
% 4.05/1.00  inst_num_of_non_proper_insts:           1533
% 4.05/1.00  inst_num_of_duplicates:                 0
% 4.05/1.00  inst_inst_num_from_inst_to_res:         0
% 4.05/1.00  inst_dismatching_checking_time:         0.
% 4.05/1.00  
% 4.05/1.00  ------ Resolution
% 4.05/1.00  
% 4.05/1.00  res_num_of_clauses:                     0
% 4.05/1.00  res_num_in_passive:                     0
% 4.05/1.00  res_num_in_active:                      0
% 4.05/1.00  res_num_of_loops:                       137
% 4.05/1.00  res_forward_subset_subsumed:            136
% 4.05/1.00  res_backward_subset_subsumed:           0
% 4.05/1.00  res_forward_subsumed:                   0
% 4.05/1.00  res_backward_subsumed:                  0
% 4.05/1.00  res_forward_subsumption_resolution:     0
% 4.05/1.00  res_backward_subsumption_resolution:    0
% 4.05/1.00  res_clause_to_clause_subsumption:       421
% 4.05/1.00  res_orphan_elimination:                 0
% 4.05/1.00  res_tautology_del:                      143
% 4.05/1.00  res_num_eq_res_simplified:              0
% 4.05/1.00  res_num_sel_changes:                    0
% 4.05/1.00  res_moves_from_active_to_pass:          0
% 4.05/1.00  
% 4.05/1.00  ------ Superposition
% 4.05/1.00  
% 4.05/1.00  sup_time_total:                         0.
% 4.05/1.00  sup_time_generating:                    0.
% 4.05/1.00  sup_time_sim_full:                      0.
% 4.05/1.00  sup_time_sim_immed:                     0.
% 4.05/1.00  
% 4.05/1.00  sup_num_of_clauses:                     148
% 4.05/1.00  sup_num_in_active:                      99
% 4.05/1.00  sup_num_in_passive:                     49
% 4.05/1.00  sup_num_of_loops:                       99
% 4.05/1.00  sup_fw_superposition:                   124
% 4.05/1.00  sup_bw_superposition:                   75
% 4.05/1.00  sup_immediate_simplified:               73
% 4.05/1.00  sup_given_eliminated:                   0
% 4.05/1.00  comparisons_done:                       0
% 4.05/1.00  comparisons_avoided:                    0
% 4.05/1.00  
% 4.05/1.00  ------ Simplifications
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  sim_fw_subset_subsumed:                 3
% 4.05/1.00  sim_bw_subset_subsumed:                 1
% 4.05/1.00  sim_fw_subsumed:                        22
% 4.05/1.00  sim_bw_subsumed:                        1
% 4.05/1.00  sim_fw_subsumption_res:                 0
% 4.05/1.00  sim_bw_subsumption_res:                 0
% 4.05/1.00  sim_tautology_del:                      2
% 4.05/1.00  sim_eq_tautology_del:                   31
% 4.05/1.00  sim_eq_res_simp:                        0
% 4.05/1.00  sim_fw_demodulated:                     17
% 4.05/1.00  sim_bw_demodulated:                     0
% 4.05/1.00  sim_light_normalised:                   65
% 4.05/1.00  sim_joinable_taut:                      0
% 4.05/1.00  sim_joinable_simp:                      0
% 4.05/1.00  sim_ac_normalised:                      0
% 4.05/1.00  sim_smt_subsumption:                    0
% 4.05/1.00  
%------------------------------------------------------------------------------
