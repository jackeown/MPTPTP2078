%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:25 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 164 expanded)
%              Number of clauses        :   39 (  41 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  325 ( 605 expanded)
%              Number of equality atoms :  186 ( 328 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK6,sK5) != sK4
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_funct_1(sK6,sK5) != sK4
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f36])).

fof(f75,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f91,plain,(
    v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f73,f79])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f72,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f77])).

fof(f98,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f77])).

fof(f96,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f97,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f76,plain,(
    k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3108,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_385,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_32])).

cnf(c_386,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK6,X2),X1)
    | ~ v1_funct_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_390,plain,
    ( r2_hidden(k1_funct_1(sK6,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK6,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_34])).

cnf(c_391,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK6,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK6,X0),X2)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X1
    | sK6 != sK6
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_391])).

cnf(c_419,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1405,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_419])).

cnf(c_3102,plain,
    ( k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3123,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4795,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k1_funct_1(sK6,X0) = sK4
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_3123])).

cnf(c_6,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_88,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_90,plain,
    ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_348,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_349,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_23,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3142,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_349,c_23,c_24])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,k2_relat_1(k6_relat_1(X1)))
    | k10_relat_1(k6_relat_1(X1),k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1465,plain,
    ( ~ r2_hidden(X0,k2_relat_1(k6_relat_1(X1)))
    | k10_relat_1(k6_relat_1(X1),k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_355])).

cnf(c_3107,plain,
    ( k10_relat_1(k6_relat_1(X0),k3_enumset1(X1,X1,X1,X1,X1)) != k1_xboole_0
    | r2_hidden(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_3176,plain,
    ( k10_relat_1(k6_relat_1(X0),k3_enumset1(X1,X1,X1,X1,X1)) != k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3107,c_23])).

cnf(c_4414,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0
    | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_3176])).

cnf(c_4416,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
    | r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4414])).

cnf(c_4973,plain,
    ( k1_funct_1(sK6,X0) = sK4
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4795,c_90,c_4416])).

cnf(c_4981,plain,
    ( k1_funct_1(sK6,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_3108,c_4973])).

cnf(c_30,negated_conjecture,
    ( k1_funct_1(sK6,sK5) != sK4 ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4981,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:41:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.33/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.01  
% 2.33/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/1.01  
% 2.33/1.01  ------  iProver source info
% 2.33/1.01  
% 2.33/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.33/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/1.01  git: non_committed_changes: false
% 2.33/1.01  git: last_make_outside_of_git: false
% 2.33/1.01  
% 2.33/1.01  ------ 
% 2.33/1.01  
% 2.33/1.01  ------ Input Options
% 2.33/1.01  
% 2.33/1.01  --out_options                           all
% 2.33/1.01  --tptp_safe_out                         true
% 2.33/1.01  --problem_path                          ""
% 2.33/1.01  --include_path                          ""
% 2.33/1.01  --clausifier                            res/vclausify_rel
% 2.33/1.01  --clausifier_options                    --mode clausify
% 2.33/1.01  --stdin                                 false
% 2.33/1.01  --stats_out                             all
% 2.33/1.01  
% 2.33/1.01  ------ General Options
% 2.33/1.01  
% 2.33/1.01  --fof                                   false
% 2.33/1.01  --time_out_real                         305.
% 2.33/1.01  --time_out_virtual                      -1.
% 2.33/1.01  --symbol_type_check                     false
% 2.33/1.01  --clausify_out                          false
% 2.33/1.01  --sig_cnt_out                           false
% 2.33/1.01  --trig_cnt_out                          false
% 2.33/1.01  --trig_cnt_out_tolerance                1.
% 2.33/1.01  --trig_cnt_out_sk_spl                   false
% 2.33/1.01  --abstr_cl_out                          false
% 2.33/1.01  
% 2.33/1.01  ------ Global Options
% 2.33/1.01  
% 2.33/1.01  --schedule                              default
% 2.33/1.01  --add_important_lit                     false
% 2.33/1.01  --prop_solver_per_cl                    1000
% 2.33/1.01  --min_unsat_core                        false
% 2.33/1.01  --soft_assumptions                      false
% 2.33/1.01  --soft_lemma_size                       3
% 2.33/1.01  --prop_impl_unit_size                   0
% 2.33/1.01  --prop_impl_unit                        []
% 2.33/1.01  --share_sel_clauses                     true
% 2.33/1.01  --reset_solvers                         false
% 2.33/1.01  --bc_imp_inh                            [conj_cone]
% 2.33/1.01  --conj_cone_tolerance                   3.
% 2.33/1.01  --extra_neg_conj                        none
% 2.33/1.01  --large_theory_mode                     true
% 2.33/1.01  --prolific_symb_bound                   200
% 2.33/1.01  --lt_threshold                          2000
% 2.33/1.01  --clause_weak_htbl                      true
% 2.33/1.01  --gc_record_bc_elim                     false
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing Options
% 2.33/1.01  
% 2.33/1.01  --preprocessing_flag                    true
% 2.33/1.01  --time_out_prep_mult                    0.1
% 2.33/1.01  --splitting_mode                        input
% 2.33/1.01  --splitting_grd                         true
% 2.33/1.01  --splitting_cvd                         false
% 2.33/1.01  --splitting_cvd_svl                     false
% 2.33/1.01  --splitting_nvd                         32
% 2.33/1.01  --sub_typing                            true
% 2.33/1.01  --prep_gs_sim                           true
% 2.33/1.01  --prep_unflatten                        true
% 2.33/1.01  --prep_res_sim                          true
% 2.33/1.01  --prep_upred                            true
% 2.33/1.01  --prep_sem_filter                       exhaustive
% 2.33/1.01  --prep_sem_filter_out                   false
% 2.33/1.01  --pred_elim                             true
% 2.33/1.01  --res_sim_input                         true
% 2.33/1.01  --eq_ax_congr_red                       true
% 2.33/1.01  --pure_diseq_elim                       true
% 2.33/1.01  --brand_transform                       false
% 2.33/1.01  --non_eq_to_eq                          false
% 2.33/1.01  --prep_def_merge                        true
% 2.33/1.01  --prep_def_merge_prop_impl              false
% 2.33/1.01  --prep_def_merge_mbd                    true
% 2.33/1.01  --prep_def_merge_tr_red                 false
% 2.33/1.01  --prep_def_merge_tr_cl                  false
% 2.33/1.01  --smt_preprocessing                     true
% 2.33/1.01  --smt_ac_axioms                         fast
% 2.33/1.01  --preprocessed_out                      false
% 2.33/1.01  --preprocessed_stats                    false
% 2.33/1.01  
% 2.33/1.01  ------ Abstraction refinement Options
% 2.33/1.01  
% 2.33/1.01  --abstr_ref                             []
% 2.33/1.01  --abstr_ref_prep                        false
% 2.33/1.01  --abstr_ref_until_sat                   false
% 2.33/1.01  --abstr_ref_sig_restrict                funpre
% 2.33/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.01  --abstr_ref_under                       []
% 2.33/1.01  
% 2.33/1.01  ------ SAT Options
% 2.33/1.01  
% 2.33/1.01  --sat_mode                              false
% 2.33/1.01  --sat_fm_restart_options                ""
% 2.33/1.01  --sat_gr_def                            false
% 2.33/1.01  --sat_epr_types                         true
% 2.33/1.01  --sat_non_cyclic_types                  false
% 2.33/1.01  --sat_finite_models                     false
% 2.33/1.01  --sat_fm_lemmas                         false
% 2.33/1.01  --sat_fm_prep                           false
% 2.33/1.01  --sat_fm_uc_incr                        true
% 2.33/1.01  --sat_out_model                         small
% 2.33/1.01  --sat_out_clauses                       false
% 2.33/1.01  
% 2.33/1.01  ------ QBF Options
% 2.33/1.01  
% 2.33/1.01  --qbf_mode                              false
% 2.33/1.01  --qbf_elim_univ                         false
% 2.33/1.01  --qbf_dom_inst                          none
% 2.33/1.01  --qbf_dom_pre_inst                      false
% 2.33/1.01  --qbf_sk_in                             false
% 2.33/1.01  --qbf_pred_elim                         true
% 2.33/1.01  --qbf_split                             512
% 2.33/1.01  
% 2.33/1.01  ------ BMC1 Options
% 2.33/1.01  
% 2.33/1.01  --bmc1_incremental                      false
% 2.33/1.01  --bmc1_axioms                           reachable_all
% 2.33/1.01  --bmc1_min_bound                        0
% 2.33/1.01  --bmc1_max_bound                        -1
% 2.33/1.01  --bmc1_max_bound_default                -1
% 2.33/1.01  --bmc1_symbol_reachability              true
% 2.33/1.01  --bmc1_property_lemmas                  false
% 2.33/1.01  --bmc1_k_induction                      false
% 2.33/1.01  --bmc1_non_equiv_states                 false
% 2.33/1.01  --bmc1_deadlock                         false
% 2.33/1.01  --bmc1_ucm                              false
% 2.33/1.01  --bmc1_add_unsat_core                   none
% 2.33/1.01  --bmc1_unsat_core_children              false
% 2.33/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.01  --bmc1_out_stat                         full
% 2.33/1.01  --bmc1_ground_init                      false
% 2.33/1.01  --bmc1_pre_inst_next_state              false
% 2.33/1.01  --bmc1_pre_inst_state                   false
% 2.33/1.01  --bmc1_pre_inst_reach_state             false
% 2.33/1.01  --bmc1_out_unsat_core                   false
% 2.33/1.01  --bmc1_aig_witness_out                  false
% 2.33/1.01  --bmc1_verbose                          false
% 2.33/1.01  --bmc1_dump_clauses_tptp                false
% 2.33/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.01  --bmc1_dump_file                        -
% 2.33/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.01  --bmc1_ucm_extend_mode                  1
% 2.33/1.01  --bmc1_ucm_init_mode                    2
% 2.33/1.01  --bmc1_ucm_cone_mode                    none
% 2.33/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.01  --bmc1_ucm_relax_model                  4
% 2.33/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.01  --bmc1_ucm_layered_model                none
% 2.33/1.01  --bmc1_ucm_max_lemma_size               10
% 2.33/1.01  
% 2.33/1.01  ------ AIG Options
% 2.33/1.01  
% 2.33/1.01  --aig_mode                              false
% 2.33/1.01  
% 2.33/1.01  ------ Instantiation Options
% 2.33/1.01  
% 2.33/1.01  --instantiation_flag                    true
% 2.33/1.01  --inst_sos_flag                         false
% 2.33/1.01  --inst_sos_phase                        true
% 2.33/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.01  --inst_lit_sel_side                     num_symb
% 2.33/1.01  --inst_solver_per_active                1400
% 2.33/1.01  --inst_solver_calls_frac                1.
% 2.33/1.01  --inst_passive_queue_type               priority_queues
% 2.33/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.01  --inst_passive_queues_freq              [25;2]
% 2.33/1.01  --inst_dismatching                      true
% 2.33/1.01  --inst_eager_unprocessed_to_passive     true
% 2.33/1.01  --inst_prop_sim_given                   true
% 2.33/1.01  --inst_prop_sim_new                     false
% 2.33/1.01  --inst_subs_new                         false
% 2.33/1.01  --inst_eq_res_simp                      false
% 2.33/1.01  --inst_subs_given                       false
% 2.33/1.01  --inst_orphan_elimination               true
% 2.33/1.01  --inst_learning_loop_flag               true
% 2.33/1.01  --inst_learning_start                   3000
% 2.33/1.01  --inst_learning_factor                  2
% 2.33/1.01  --inst_start_prop_sim_after_learn       3
% 2.33/1.01  --inst_sel_renew                        solver
% 2.33/1.01  --inst_lit_activity_flag                true
% 2.33/1.01  --inst_restr_to_given                   false
% 2.33/1.01  --inst_activity_threshold               500
% 2.33/1.01  --inst_out_proof                        true
% 2.33/1.01  
% 2.33/1.01  ------ Resolution Options
% 2.33/1.01  
% 2.33/1.01  --resolution_flag                       true
% 2.33/1.01  --res_lit_sel                           adaptive
% 2.33/1.01  --res_lit_sel_side                      none
% 2.33/1.01  --res_ordering                          kbo
% 2.33/1.01  --res_to_prop_solver                    active
% 2.33/1.01  --res_prop_simpl_new                    false
% 2.33/1.01  --res_prop_simpl_given                  true
% 2.33/1.01  --res_passive_queue_type                priority_queues
% 2.33/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.01  --res_passive_queues_freq               [15;5]
% 2.33/1.01  --res_forward_subs                      full
% 2.33/1.01  --res_backward_subs                     full
% 2.33/1.01  --res_forward_subs_resolution           true
% 2.33/1.01  --res_backward_subs_resolution          true
% 2.33/1.01  --res_orphan_elimination                true
% 2.33/1.01  --res_time_limit                        2.
% 2.33/1.01  --res_out_proof                         true
% 2.33/1.01  
% 2.33/1.01  ------ Superposition Options
% 2.33/1.01  
% 2.33/1.01  --superposition_flag                    true
% 2.33/1.01  --sup_passive_queue_type                priority_queues
% 2.33/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.01  --demod_completeness_check              fast
% 2.33/1.01  --demod_use_ground                      true
% 2.33/1.01  --sup_to_prop_solver                    passive
% 2.33/1.01  --sup_prop_simpl_new                    true
% 2.33/1.01  --sup_prop_simpl_given                  true
% 2.33/1.01  --sup_fun_splitting                     false
% 2.33/1.01  --sup_smt_interval                      50000
% 2.33/1.01  
% 2.33/1.01  ------ Superposition Simplification Setup
% 2.33/1.01  
% 2.33/1.01  --sup_indices_passive                   []
% 2.33/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_full_bw                           [BwDemod]
% 2.33/1.01  --sup_immed_triv                        [TrivRules]
% 2.33/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_immed_bw_main                     []
% 2.33/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.01  
% 2.33/1.01  ------ Combination Options
% 2.33/1.01  
% 2.33/1.01  --comb_res_mult                         3
% 2.33/1.01  --comb_sup_mult                         2
% 2.33/1.01  --comb_inst_mult                        10
% 2.33/1.01  
% 2.33/1.01  ------ Debug Options
% 2.33/1.01  
% 2.33/1.01  --dbg_backtrace                         false
% 2.33/1.01  --dbg_dump_prop_clauses                 false
% 2.33/1.01  --dbg_dump_prop_clauses_file            -
% 2.33/1.01  --dbg_out_stat                          false
% 2.33/1.01  ------ Parsing...
% 2.33/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/1.01  
% 2.33/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/1.01  ------ Proving...
% 2.33/1.01  ------ Problem Properties 
% 2.33/1.01  
% 2.33/1.01  
% 2.33/1.01  clauses                                 30
% 2.33/1.01  conjectures                             2
% 2.33/1.02  EPR                                     7
% 2.33/1.02  Horn                                    24
% 2.33/1.02  unary                                   9
% 2.33/1.02  binary                                  8
% 2.33/1.02  lits                                    75
% 2.33/1.02  lits eq                                 36
% 2.33/1.02  fd_pure                                 0
% 2.33/1.02  fd_pseudo                               0
% 2.33/1.02  fd_cond                                 0
% 2.33/1.02  fd_pseudo_cond                          6
% 2.33/1.02  AC symbols                              0
% 2.33/1.02  
% 2.33/1.02  ------ Schedule dynamic 5 is on 
% 2.33/1.02  
% 2.33/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/1.02  
% 2.33/1.02  
% 2.33/1.02  ------ 
% 2.33/1.02  Current options:
% 2.33/1.02  ------ 
% 2.33/1.02  
% 2.33/1.02  ------ Input Options
% 2.33/1.02  
% 2.33/1.02  --out_options                           all
% 2.33/1.02  --tptp_safe_out                         true
% 2.33/1.02  --problem_path                          ""
% 2.33/1.02  --include_path                          ""
% 2.33/1.02  --clausifier                            res/vclausify_rel
% 2.33/1.02  --clausifier_options                    --mode clausify
% 2.33/1.02  --stdin                                 false
% 2.33/1.02  --stats_out                             all
% 2.33/1.02  
% 2.33/1.02  ------ General Options
% 2.33/1.02  
% 2.33/1.02  --fof                                   false
% 2.33/1.02  --time_out_real                         305.
% 2.33/1.02  --time_out_virtual                      -1.
% 2.33/1.02  --symbol_type_check                     false
% 2.33/1.02  --clausify_out                          false
% 2.33/1.02  --sig_cnt_out                           false
% 2.33/1.02  --trig_cnt_out                          false
% 2.33/1.02  --trig_cnt_out_tolerance                1.
% 2.33/1.02  --trig_cnt_out_sk_spl                   false
% 2.33/1.02  --abstr_cl_out                          false
% 2.33/1.02  
% 2.33/1.02  ------ Global Options
% 2.33/1.02  
% 2.33/1.02  --schedule                              default
% 2.33/1.02  --add_important_lit                     false
% 2.33/1.02  --prop_solver_per_cl                    1000
% 2.33/1.02  --min_unsat_core                        false
% 2.33/1.02  --soft_assumptions                      false
% 2.33/1.02  --soft_lemma_size                       3
% 2.33/1.02  --prop_impl_unit_size                   0
% 2.33/1.02  --prop_impl_unit                        []
% 2.33/1.02  --share_sel_clauses                     true
% 2.33/1.02  --reset_solvers                         false
% 2.33/1.02  --bc_imp_inh                            [conj_cone]
% 2.33/1.02  --conj_cone_tolerance                   3.
% 2.33/1.02  --extra_neg_conj                        none
% 2.33/1.02  --large_theory_mode                     true
% 2.33/1.02  --prolific_symb_bound                   200
% 2.33/1.02  --lt_threshold                          2000
% 2.33/1.02  --clause_weak_htbl                      true
% 2.33/1.02  --gc_record_bc_elim                     false
% 2.33/1.02  
% 2.33/1.02  ------ Preprocessing Options
% 2.33/1.02  
% 2.33/1.02  --preprocessing_flag                    true
% 2.33/1.02  --time_out_prep_mult                    0.1
% 2.33/1.02  --splitting_mode                        input
% 2.33/1.02  --splitting_grd                         true
% 2.33/1.02  --splitting_cvd                         false
% 2.33/1.02  --splitting_cvd_svl                     false
% 2.33/1.02  --splitting_nvd                         32
% 2.33/1.02  --sub_typing                            true
% 2.33/1.02  --prep_gs_sim                           true
% 2.33/1.02  --prep_unflatten                        true
% 2.33/1.02  --prep_res_sim                          true
% 2.33/1.02  --prep_upred                            true
% 2.33/1.02  --prep_sem_filter                       exhaustive
% 2.33/1.02  --prep_sem_filter_out                   false
% 2.33/1.02  --pred_elim                             true
% 2.33/1.02  --res_sim_input                         true
% 2.33/1.02  --eq_ax_congr_red                       true
% 2.33/1.02  --pure_diseq_elim                       true
% 2.33/1.02  --brand_transform                       false
% 2.33/1.02  --non_eq_to_eq                          false
% 2.33/1.02  --prep_def_merge                        true
% 2.33/1.02  --prep_def_merge_prop_impl              false
% 2.33/1.02  --prep_def_merge_mbd                    true
% 2.33/1.02  --prep_def_merge_tr_red                 false
% 2.33/1.02  --prep_def_merge_tr_cl                  false
% 2.33/1.02  --smt_preprocessing                     true
% 2.33/1.02  --smt_ac_axioms                         fast
% 2.33/1.02  --preprocessed_out                      false
% 2.33/1.02  --preprocessed_stats                    false
% 2.33/1.02  
% 2.33/1.02  ------ Abstraction refinement Options
% 2.33/1.02  
% 2.33/1.02  --abstr_ref                             []
% 2.33/1.02  --abstr_ref_prep                        false
% 2.33/1.02  --abstr_ref_until_sat                   false
% 2.33/1.02  --abstr_ref_sig_restrict                funpre
% 2.33/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.02  --abstr_ref_under                       []
% 2.33/1.02  
% 2.33/1.02  ------ SAT Options
% 2.33/1.02  
% 2.33/1.02  --sat_mode                              false
% 2.33/1.02  --sat_fm_restart_options                ""
% 2.33/1.02  --sat_gr_def                            false
% 2.33/1.02  --sat_epr_types                         true
% 2.33/1.02  --sat_non_cyclic_types                  false
% 2.33/1.02  --sat_finite_models                     false
% 2.33/1.02  --sat_fm_lemmas                         false
% 2.33/1.02  --sat_fm_prep                           false
% 2.33/1.02  --sat_fm_uc_incr                        true
% 2.33/1.02  --sat_out_model                         small
% 2.33/1.02  --sat_out_clauses                       false
% 2.33/1.02  
% 2.33/1.02  ------ QBF Options
% 2.33/1.02  
% 2.33/1.02  --qbf_mode                              false
% 2.33/1.02  --qbf_elim_univ                         false
% 2.33/1.02  --qbf_dom_inst                          none
% 2.33/1.02  --qbf_dom_pre_inst                      false
% 2.33/1.02  --qbf_sk_in                             false
% 2.33/1.02  --qbf_pred_elim                         true
% 2.33/1.02  --qbf_split                             512
% 2.33/1.02  
% 2.33/1.02  ------ BMC1 Options
% 2.33/1.02  
% 2.33/1.02  --bmc1_incremental                      false
% 2.33/1.02  --bmc1_axioms                           reachable_all
% 2.33/1.02  --bmc1_min_bound                        0
% 2.33/1.02  --bmc1_max_bound                        -1
% 2.33/1.02  --bmc1_max_bound_default                -1
% 2.33/1.02  --bmc1_symbol_reachability              true
% 2.33/1.02  --bmc1_property_lemmas                  false
% 2.33/1.02  --bmc1_k_induction                      false
% 2.33/1.02  --bmc1_non_equiv_states                 false
% 2.33/1.02  --bmc1_deadlock                         false
% 2.33/1.02  --bmc1_ucm                              false
% 2.33/1.02  --bmc1_add_unsat_core                   none
% 2.33/1.02  --bmc1_unsat_core_children              false
% 2.33/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.02  --bmc1_out_stat                         full
% 2.33/1.02  --bmc1_ground_init                      false
% 2.33/1.02  --bmc1_pre_inst_next_state              false
% 2.33/1.02  --bmc1_pre_inst_state                   false
% 2.33/1.02  --bmc1_pre_inst_reach_state             false
% 2.33/1.02  --bmc1_out_unsat_core                   false
% 2.33/1.02  --bmc1_aig_witness_out                  false
% 2.33/1.02  --bmc1_verbose                          false
% 2.33/1.02  --bmc1_dump_clauses_tptp                false
% 2.33/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.02  --bmc1_dump_file                        -
% 2.33/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.02  --bmc1_ucm_extend_mode                  1
% 2.33/1.02  --bmc1_ucm_init_mode                    2
% 2.33/1.02  --bmc1_ucm_cone_mode                    none
% 2.33/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.02  --bmc1_ucm_relax_model                  4
% 2.33/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.02  --bmc1_ucm_layered_model                none
% 2.33/1.02  --bmc1_ucm_max_lemma_size               10
% 2.33/1.02  
% 2.33/1.02  ------ AIG Options
% 2.33/1.02  
% 2.33/1.02  --aig_mode                              false
% 2.33/1.02  
% 2.33/1.02  ------ Instantiation Options
% 2.33/1.02  
% 2.33/1.02  --instantiation_flag                    true
% 2.33/1.02  --inst_sos_flag                         false
% 2.33/1.02  --inst_sos_phase                        true
% 2.33/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.02  --inst_lit_sel_side                     none
% 2.33/1.02  --inst_solver_per_active                1400
% 2.33/1.02  --inst_solver_calls_frac                1.
% 2.33/1.02  --inst_passive_queue_type               priority_queues
% 2.33/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.02  --inst_passive_queues_freq              [25;2]
% 2.33/1.02  --inst_dismatching                      true
% 2.33/1.02  --inst_eager_unprocessed_to_passive     true
% 2.33/1.02  --inst_prop_sim_given                   true
% 2.33/1.02  --inst_prop_sim_new                     false
% 2.33/1.02  --inst_subs_new                         false
% 2.33/1.02  --inst_eq_res_simp                      false
% 2.33/1.02  --inst_subs_given                       false
% 2.33/1.02  --inst_orphan_elimination               true
% 2.33/1.02  --inst_learning_loop_flag               true
% 2.33/1.02  --inst_learning_start                   3000
% 2.33/1.02  --inst_learning_factor                  2
% 2.33/1.02  --inst_start_prop_sim_after_learn       3
% 2.33/1.02  --inst_sel_renew                        solver
% 2.33/1.02  --inst_lit_activity_flag                true
% 2.33/1.02  --inst_restr_to_given                   false
% 2.33/1.02  --inst_activity_threshold               500
% 2.33/1.02  --inst_out_proof                        true
% 2.33/1.02  
% 2.33/1.02  ------ Resolution Options
% 2.33/1.02  
% 2.33/1.02  --resolution_flag                       false
% 2.33/1.02  --res_lit_sel                           adaptive
% 2.33/1.02  --res_lit_sel_side                      none
% 2.33/1.02  --res_ordering                          kbo
% 2.33/1.02  --res_to_prop_solver                    active
% 2.33/1.02  --res_prop_simpl_new                    false
% 2.33/1.02  --res_prop_simpl_given                  true
% 2.33/1.02  --res_passive_queue_type                priority_queues
% 2.33/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.02  --res_passive_queues_freq               [15;5]
% 2.33/1.02  --res_forward_subs                      full
% 2.33/1.02  --res_backward_subs                     full
% 2.33/1.02  --res_forward_subs_resolution           true
% 2.33/1.02  --res_backward_subs_resolution          true
% 2.33/1.02  --res_orphan_elimination                true
% 2.33/1.02  --res_time_limit                        2.
% 2.33/1.02  --res_out_proof                         true
% 2.33/1.02  
% 2.33/1.02  ------ Superposition Options
% 2.33/1.02  
% 2.33/1.02  --superposition_flag                    true
% 2.33/1.02  --sup_passive_queue_type                priority_queues
% 2.33/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.02  --demod_completeness_check              fast
% 2.33/1.02  --demod_use_ground                      true
% 2.33/1.02  --sup_to_prop_solver                    passive
% 2.33/1.02  --sup_prop_simpl_new                    true
% 2.33/1.02  --sup_prop_simpl_given                  true
% 2.33/1.02  --sup_fun_splitting                     false
% 2.33/1.02  --sup_smt_interval                      50000
% 2.33/1.02  
% 2.33/1.02  ------ Superposition Simplification Setup
% 2.33/1.02  
% 2.33/1.02  --sup_indices_passive                   []
% 2.33/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.02  --sup_full_bw                           [BwDemod]
% 2.33/1.02  --sup_immed_triv                        [TrivRules]
% 2.33/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.02  --sup_immed_bw_main                     []
% 2.33/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.02  
% 2.33/1.02  ------ Combination Options
% 2.33/1.02  
% 2.33/1.02  --comb_res_mult                         3
% 2.33/1.02  --comb_sup_mult                         2
% 2.33/1.02  --comb_inst_mult                        10
% 2.33/1.02  
% 2.33/1.02  ------ Debug Options
% 2.33/1.02  
% 2.33/1.02  --dbg_backtrace                         false
% 2.33/1.02  --dbg_dump_prop_clauses                 false
% 2.33/1.02  --dbg_dump_prop_clauses_file            -
% 2.33/1.02  --dbg_out_stat                          false
% 2.33/1.02  
% 2.33/1.02  
% 2.33/1.02  
% 2.33/1.02  
% 2.33/1.02  ------ Proving...
% 2.33/1.02  
% 2.33/1.02  
% 2.33/1.02  % SZS status Theorem for theBenchmark.p
% 2.33/1.02  
% 2.33/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.02  
% 2.33/1.02  fof(f12,conjecture,(
% 2.33/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f13,negated_conjecture,(
% 2.33/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 2.33/1.02    inference(negated_conjecture,[],[f12])).
% 2.33/1.02  
% 2.33/1.02  fof(f20,plain,(
% 2.33/1.02    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 2.33/1.02    inference(ennf_transformation,[],[f13])).
% 2.33/1.02  
% 2.33/1.02  fof(f21,plain,(
% 2.33/1.02    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 2.33/1.02    inference(flattening,[],[f20])).
% 2.33/1.02  
% 2.33/1.02  fof(f36,plain,(
% 2.33/1.02    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 2.33/1.02    introduced(choice_axiom,[])).
% 2.33/1.02  
% 2.33/1.02  fof(f37,plain,(
% 2.33/1.02    k1_funct_1(sK6,sK5) != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 2.33/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f36])).
% 2.33/1.02  
% 2.33/1.02  fof(f75,plain,(
% 2.33/1.02    r2_hidden(sK5,sK3)),
% 2.33/1.02    inference(cnf_transformation,[],[f37])).
% 2.33/1.02  
% 2.33/1.02  fof(f73,plain,(
% 2.33/1.02    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 2.33/1.02    inference(cnf_transformation,[],[f37])).
% 2.33/1.02  
% 2.33/1.02  fof(f2,axiom,(
% 2.33/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f46,plain,(
% 2.33/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.33/1.02    inference(cnf_transformation,[],[f2])).
% 2.33/1.02  
% 2.33/1.02  fof(f3,axiom,(
% 2.33/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f47,plain,(
% 2.33/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.33/1.02    inference(cnf_transformation,[],[f3])).
% 2.33/1.02  
% 2.33/1.02  fof(f4,axiom,(
% 2.33/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f48,plain,(
% 2.33/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.33/1.02    inference(cnf_transformation,[],[f4])).
% 2.33/1.02  
% 2.33/1.02  fof(f5,axiom,(
% 2.33/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f49,plain,(
% 2.33/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.33/1.02    inference(cnf_transformation,[],[f5])).
% 2.33/1.02  
% 2.33/1.02  fof(f77,plain,(
% 2.33/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.33/1.02    inference(definition_unfolding,[],[f48,f49])).
% 2.33/1.02  
% 2.33/1.02  fof(f78,plain,(
% 2.33/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.33/1.02    inference(definition_unfolding,[],[f47,f77])).
% 2.33/1.02  
% 2.33/1.02  fof(f79,plain,(
% 2.33/1.02    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.33/1.02    inference(definition_unfolding,[],[f46,f78])).
% 2.33/1.02  
% 2.33/1.02  fof(f91,plain,(
% 2.33/1.02    v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 2.33/1.02    inference(definition_unfolding,[],[f73,f79])).
% 2.33/1.02  
% 2.33/1.02  fof(f11,axiom,(
% 2.33/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f18,plain,(
% 2.33/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.33/1.02    inference(ennf_transformation,[],[f11])).
% 2.33/1.02  
% 2.33/1.02  fof(f19,plain,(
% 2.33/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.33/1.02    inference(flattening,[],[f18])).
% 2.33/1.02  
% 2.33/1.02  fof(f71,plain,(
% 2.33/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.33/1.02    inference(cnf_transformation,[],[f19])).
% 2.33/1.02  
% 2.33/1.02  fof(f74,plain,(
% 2.33/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 2.33/1.02    inference(cnf_transformation,[],[f37])).
% 2.33/1.02  
% 2.33/1.02  fof(f90,plain,(
% 2.33/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))),
% 2.33/1.02    inference(definition_unfolding,[],[f74,f79])).
% 2.33/1.02  
% 2.33/1.02  fof(f72,plain,(
% 2.33/1.02    v1_funct_1(sK6)),
% 2.33/1.02    inference(cnf_transformation,[],[f37])).
% 2.33/1.02  
% 2.33/1.02  fof(f1,axiom,(
% 2.33/1.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f14,plain,(
% 2.33/1.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.33/1.02    inference(ennf_transformation,[],[f1])).
% 2.33/1.02  
% 2.33/1.02  fof(f24,plain,(
% 2.33/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/1.02    inference(nnf_transformation,[],[f14])).
% 2.33/1.02  
% 2.33/1.02  fof(f25,plain,(
% 2.33/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/1.02    inference(flattening,[],[f24])).
% 2.33/1.02  
% 2.33/1.02  fof(f26,plain,(
% 2.33/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/1.02    inference(rectify,[],[f25])).
% 2.33/1.02  
% 2.33/1.02  fof(f27,plain,(
% 2.33/1.02    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.33/1.02    introduced(choice_axiom,[])).
% 2.33/1.02  
% 2.33/1.02  fof(f28,plain,(
% 2.33/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.33/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.33/1.02  
% 2.33/1.02  fof(f38,plain,(
% 2.33/1.02    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.33/1.02    inference(cnf_transformation,[],[f28])).
% 2.33/1.02  
% 2.33/1.02  fof(f87,plain,(
% 2.33/1.02    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.33/1.02    inference(definition_unfolding,[],[f38,f77])).
% 2.33/1.02  
% 2.33/1.02  fof(f98,plain,(
% 2.33/1.02    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 2.33/1.02    inference(equality_resolution,[],[f87])).
% 2.33/1.02  
% 2.33/1.02  fof(f39,plain,(
% 2.33/1.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.33/1.02    inference(cnf_transformation,[],[f28])).
% 2.33/1.02  
% 2.33/1.02  fof(f86,plain,(
% 2.33/1.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.33/1.02    inference(definition_unfolding,[],[f39,f77])).
% 2.33/1.02  
% 2.33/1.02  fof(f96,plain,(
% 2.33/1.02    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 2.33/1.02    inference(equality_resolution,[],[f86])).
% 2.33/1.02  
% 2.33/1.02  fof(f97,plain,(
% 2.33/1.02    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 2.33/1.02    inference(equality_resolution,[],[f96])).
% 2.33/1.02  
% 2.33/1.02  fof(f7,axiom,(
% 2.33/1.02    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f16,plain,(
% 2.33/1.02    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.33/1.02    inference(ennf_transformation,[],[f7])).
% 2.33/1.02  
% 2.33/1.02  fof(f64,plain,(
% 2.33/1.02    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/1.02    inference(cnf_transformation,[],[f16])).
% 2.33/1.02  
% 2.33/1.02  fof(f9,axiom,(
% 2.33/1.02    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f67,plain,(
% 2.33/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.33/1.02    inference(cnf_transformation,[],[f9])).
% 2.33/1.02  
% 2.33/1.02  fof(f8,axiom,(
% 2.33/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f66,plain,(
% 2.33/1.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.33/1.02    inference(cnf_transformation,[],[f8])).
% 2.33/1.02  
% 2.33/1.02  fof(f65,plain,(
% 2.33/1.02    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.33/1.02    inference(cnf_transformation,[],[f8])).
% 2.33/1.02  
% 2.33/1.02  fof(f10,axiom,(
% 2.33/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 2.33/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.02  
% 2.33/1.02  fof(f17,plain,(
% 2.33/1.02    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 2.33/1.02    inference(ennf_transformation,[],[f10])).
% 2.33/1.02  
% 2.33/1.02  fof(f35,plain,(
% 2.33/1.02    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.33/1.02    inference(nnf_transformation,[],[f17])).
% 2.33/1.02  
% 2.33/1.02  fof(f69,plain,(
% 2.33/1.02    ( ! [X0,X1] : (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.33/1.02    inference(cnf_transformation,[],[f35])).
% 2.33/1.02  
% 2.33/1.02  fof(f89,plain,(
% 2.33/1.02    ( ! [X0,X1] : (k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.33/1.02    inference(definition_unfolding,[],[f69,f79])).
% 2.33/1.02  
% 2.33/1.02  fof(f76,plain,(
% 2.33/1.02    k1_funct_1(sK6,sK5) != sK4),
% 2.33/1.02    inference(cnf_transformation,[],[f37])).
% 2.33/1.02  
% 2.33/1.02  cnf(c_31,negated_conjecture,
% 2.33/1.02      ( r2_hidden(sK5,sK3) ),
% 2.33/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_3108,plain,
% 2.33/1.02      ( r2_hidden(sK5,sK3) = iProver_top ),
% 2.33/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_33,negated_conjecture,
% 2.33/1.02      ( v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 2.33/1.02      inference(cnf_transformation,[],[f91]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_29,plain,
% 2.33/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.02      | ~ r2_hidden(X3,X1)
% 2.33/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.33/1.02      | ~ v1_funct_1(X0)
% 2.33/1.02      | k1_xboole_0 = X2 ),
% 2.33/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_32,negated_conjecture,
% 2.33/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
% 2.33/1.02      inference(cnf_transformation,[],[f90]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_385,plain,
% 2.33/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/1.02      | ~ r2_hidden(X3,X1)
% 2.33/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.33/1.02      | ~ v1_funct_1(X0)
% 2.33/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.33/1.02      | sK6 != X0
% 2.33/1.02      | k1_xboole_0 = X2 ),
% 2.33/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_32]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_386,plain,
% 2.33/1.02      ( ~ v1_funct_2(sK6,X0,X1)
% 2.33/1.02      | ~ r2_hidden(X2,X0)
% 2.33/1.02      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 2.33/1.02      | ~ v1_funct_1(sK6)
% 2.33/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.33/1.02      | k1_xboole_0 = X1 ),
% 2.33/1.02      inference(unflattening,[status(thm)],[c_385]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_34,negated_conjecture,
% 2.33/1.02      ( v1_funct_1(sK6) ),
% 2.33/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_390,plain,
% 2.33/1.02      ( r2_hidden(k1_funct_1(sK6,X2),X1)
% 2.33/1.02      | ~ r2_hidden(X2,X0)
% 2.33/1.02      | ~ v1_funct_2(sK6,X0,X1)
% 2.33/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.33/1.02      | k1_xboole_0 = X1 ),
% 2.33/1.02      inference(global_propositional_subsumption,
% 2.33/1.02                [status(thm)],
% 2.33/1.02                [c_386,c_34]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_391,plain,
% 2.33/1.02      ( ~ v1_funct_2(sK6,X0,X1)
% 2.33/1.02      | ~ r2_hidden(X2,X0)
% 2.33/1.02      | r2_hidden(k1_funct_1(sK6,X2),X1)
% 2.33/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.33/1.02      | k1_xboole_0 = X1 ),
% 2.33/1.02      inference(renaming,[status(thm)],[c_390]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_418,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,X1)
% 2.33/1.02      | r2_hidden(k1_funct_1(sK6,X0),X2)
% 2.33/1.02      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X2
% 2.33/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.33/1.02      | sK3 != X1
% 2.33/1.02      | sK6 != sK6
% 2.33/1.02      | k1_xboole_0 = X2 ),
% 2.33/1.02      inference(resolution_lifted,[status(thm)],[c_33,c_391]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_419,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,sK3)
% 2.33/1.02      | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 2.33/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))
% 2.33/1.02      | k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 2.33/1.02      inference(unflattening,[status(thm)],[c_418]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_1405,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,sK3)
% 2.33/1.02      | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 2.33/1.02      | k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 2.33/1.02      inference(equality_resolution_simp,[status(thm)],[c_419]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_3102,plain,
% 2.33/1.02      ( k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 2.33/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.33/1.02      | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.33/1.02      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_7,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 2.33/1.02      | X0 = X1
% 2.33/1.02      | X0 = X2
% 2.33/1.02      | X0 = X3 ),
% 2.33/1.02      inference(cnf_transformation,[],[f98]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_3123,plain,
% 2.33/1.02      ( X0 = X1
% 2.33/1.02      | X0 = X2
% 2.33/1.02      | X0 = X3
% 2.33/1.02      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
% 2.33/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_4795,plain,
% 2.33/1.02      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 2.33/1.02      | k1_funct_1(sK6,X0) = sK4
% 2.33/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 2.33/1.02      inference(superposition,[status(thm)],[c_3102,c_3123]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_6,plain,
% 2.33/1.02      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 2.33/1.02      inference(cnf_transformation,[],[f97]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_88,plain,
% 2.33/1.02      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 2.33/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_90,plain,
% 2.33/1.02      ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.33/1.02      inference(instantiation,[status(thm)],[c_88]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_22,plain,
% 2.33/1.02      ( ~ v1_relat_1(X0)
% 2.33/1.02      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.33/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_26,plain,
% 2.33/1.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.33/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_348,plain,
% 2.33/1.02      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 2.33/1.02      | k6_relat_1(X1) != X0 ),
% 2.33/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_349,plain,
% 2.33/1.02      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 2.33/1.02      inference(unflattening,[status(thm)],[c_348]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_23,plain,
% 2.33/1.02      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 2.33/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_24,plain,
% 2.33/1.02      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.33/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_3142,plain,
% 2.33/1.02      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 2.33/1.02      inference(light_normalisation,[status(thm)],[c_349,c_23,c_24]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_28,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.33/1.02      | ~ v1_relat_1(X1)
% 2.33/1.02      | k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0 ),
% 2.33/1.02      inference(cnf_transformation,[],[f89]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_354,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.33/1.02      | k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0
% 2.33/1.02      | k6_relat_1(X2) != X1 ),
% 2.33/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_355,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,k2_relat_1(k6_relat_1(X1)))
% 2.33/1.02      | k10_relat_1(k6_relat_1(X1),k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0 ),
% 2.33/1.02      inference(unflattening,[status(thm)],[c_354]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_1465,plain,
% 2.33/1.02      ( ~ r2_hidden(X0,k2_relat_1(k6_relat_1(X1)))
% 2.33/1.02      | k10_relat_1(k6_relat_1(X1),k3_enumset1(X0,X0,X0,X0,X0)) != k1_xboole_0 ),
% 2.33/1.02      inference(prop_impl,[status(thm)],[c_355]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_3107,plain,
% 2.33/1.02      ( k10_relat_1(k6_relat_1(X0),k3_enumset1(X1,X1,X1,X1,X1)) != k1_xboole_0
% 2.33/1.02      | r2_hidden(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
% 2.33/1.02      inference(predicate_to_equality,[status(thm)],[c_1465]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_3176,plain,
% 2.33/1.02      ( k10_relat_1(k6_relat_1(X0),k3_enumset1(X1,X1,X1,X1,X1)) != k1_xboole_0
% 2.33/1.02      | r2_hidden(X1,X0) != iProver_top ),
% 2.33/1.02      inference(light_normalisation,[status(thm)],[c_3107,c_23]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_4414,plain,
% 2.33/1.02      ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0
% 2.33/1.02      | r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.33/1.02      inference(superposition,[status(thm)],[c_3142,c_3176]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_4416,plain,
% 2.33/1.02      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
% 2.33/1.02      | r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 2.33/1.02      inference(instantiation,[status(thm)],[c_4414]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_4973,plain,
% 2.33/1.02      ( k1_funct_1(sK6,X0) = sK4 | r2_hidden(X0,sK3) != iProver_top ),
% 2.33/1.02      inference(global_propositional_subsumption,
% 2.33/1.02                [status(thm)],
% 2.33/1.02                [c_4795,c_90,c_4416]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_4981,plain,
% 2.33/1.02      ( k1_funct_1(sK6,sK5) = sK4 ),
% 2.33/1.02      inference(superposition,[status(thm)],[c_3108,c_4973]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(c_30,negated_conjecture,
% 2.33/1.02      ( k1_funct_1(sK6,sK5) != sK4 ),
% 2.33/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.33/1.02  
% 2.33/1.02  cnf(contradiction,plain,
% 2.33/1.02      ( $false ),
% 2.33/1.02      inference(minisat,[status(thm)],[c_4981,c_30]) ).
% 2.33/1.02  
% 2.33/1.02  
% 2.33/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.02  
% 2.33/1.02  ------                               Statistics
% 2.33/1.02  
% 2.33/1.02  ------ General
% 2.33/1.02  
% 2.33/1.02  abstr_ref_over_cycles:                  0
% 2.33/1.02  abstr_ref_under_cycles:                 0
% 2.33/1.02  gc_basic_clause_elim:                   0
% 2.33/1.02  forced_gc_time:                         0
% 2.33/1.02  parsing_time:                           0.009
% 2.33/1.02  unif_index_cands_time:                  0.
% 2.33/1.02  unif_index_add_time:                    0.
% 2.33/1.02  orderings_time:                         0.
% 2.33/1.02  out_proof_time:                         0.01
% 2.33/1.02  total_time:                             0.156
% 2.33/1.02  num_of_symbols:                         52
% 2.33/1.02  num_of_terms:                           3776
% 2.33/1.02  
% 2.33/1.02  ------ Preprocessing
% 2.33/1.02  
% 2.33/1.02  num_of_splits:                          0
% 2.33/1.02  num_of_split_atoms:                     0
% 2.33/1.02  num_of_reused_defs:                     0
% 2.33/1.02  num_eq_ax_congr_red:                    49
% 2.33/1.02  num_of_sem_filtered_clauses:            1
% 2.33/1.02  num_of_subtypes:                        0
% 2.33/1.02  monotx_restored_types:                  0
% 2.33/1.02  sat_num_of_epr_types:                   0
% 2.33/1.02  sat_num_of_non_cyclic_types:            0
% 2.33/1.02  sat_guarded_non_collapsed_types:        0
% 2.33/1.02  num_pure_diseq_elim:                    0
% 2.33/1.02  simp_replaced_by:                       0
% 2.33/1.02  res_preprocessed:                       144
% 2.33/1.02  prep_upred:                             0
% 2.33/1.02  prep_unflattend:                        90
% 2.33/1.02  smt_new_axioms:                         0
% 2.33/1.02  pred_elim_cands:                        2
% 2.33/1.02  pred_elim:                              4
% 2.33/1.02  pred_elim_cl:                           5
% 2.33/1.02  pred_elim_cycles:                       7
% 2.33/1.02  merged_defs:                            6
% 2.33/1.02  merged_defs_ncl:                        0
% 2.33/1.02  bin_hyper_res:                          6
% 2.33/1.02  prep_cycles:                            4
% 2.33/1.02  pred_elim_time:                         0.027
% 2.33/1.02  splitting_time:                         0.
% 2.33/1.02  sem_filter_time:                        0.
% 2.33/1.02  monotx_time:                            0.001
% 2.33/1.02  subtype_inf_time:                       0.
% 2.33/1.02  
% 2.33/1.02  ------ Problem properties
% 2.33/1.02  
% 2.33/1.02  clauses:                                30
% 2.33/1.02  conjectures:                            2
% 2.33/1.02  epr:                                    7
% 2.33/1.02  horn:                                   24
% 2.33/1.02  ground:                                 2
% 2.33/1.02  unary:                                  9
% 2.33/1.02  binary:                                 8
% 2.33/1.02  lits:                                   75
% 2.33/1.02  lits_eq:                                36
% 2.33/1.02  fd_pure:                                0
% 2.33/1.02  fd_pseudo:                              0
% 2.33/1.02  fd_cond:                                0
% 2.33/1.02  fd_pseudo_cond:                         6
% 2.33/1.02  ac_symbols:                             0
% 2.33/1.02  
% 2.33/1.02  ------ Propositional Solver
% 2.33/1.02  
% 2.33/1.02  prop_solver_calls:                      25
% 2.33/1.02  prop_fast_solver_calls:                 1194
% 2.33/1.02  smt_solver_calls:                       0
% 2.33/1.02  smt_fast_solver_calls:                  0
% 2.33/1.02  prop_num_of_clauses:                    1040
% 2.33/1.02  prop_preprocess_simplified:             6203
% 2.33/1.02  prop_fo_subsumed:                       2
% 2.33/1.02  prop_solver_time:                       0.
% 2.33/1.02  smt_solver_time:                        0.
% 2.33/1.02  smt_fast_solver_time:                   0.
% 2.33/1.02  prop_fast_solver_time:                  0.
% 2.33/1.02  prop_unsat_core_time:                   0.
% 2.33/1.02  
% 2.33/1.02  ------ QBF
% 2.33/1.02  
% 2.33/1.02  qbf_q_res:                              0
% 2.33/1.02  qbf_num_tautologies:                    0
% 2.33/1.02  qbf_prep_cycles:                        0
% 2.33/1.02  
% 2.33/1.02  ------ BMC1
% 2.33/1.02  
% 2.33/1.02  bmc1_current_bound:                     -1
% 2.33/1.02  bmc1_last_solved_bound:                 -1
% 2.33/1.02  bmc1_unsat_core_size:                   -1
% 2.33/1.02  bmc1_unsat_core_parents_size:           -1
% 2.33/1.02  bmc1_merge_next_fun:                    0
% 2.33/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.02  
% 2.33/1.02  ------ Instantiation
% 2.33/1.02  
% 2.33/1.02  inst_num_of_clauses:                    319
% 2.33/1.02  inst_num_in_passive:                    55
% 2.33/1.02  inst_num_in_active:                     123
% 2.33/1.02  inst_num_in_unprocessed:                141
% 2.33/1.02  inst_num_of_loops:                      130
% 2.33/1.02  inst_num_of_learning_restarts:          0
% 2.33/1.02  inst_num_moves_active_passive:          6
% 2.33/1.02  inst_lit_activity:                      0
% 2.33/1.02  inst_lit_activity_moves:                0
% 2.33/1.02  inst_num_tautologies:                   0
% 2.33/1.02  inst_num_prop_implied:                  0
% 2.33/1.02  inst_num_existing_simplified:           0
% 2.33/1.02  inst_num_eq_res_simplified:             0
% 2.33/1.02  inst_num_child_elim:                    0
% 2.33/1.02  inst_num_of_dismatching_blockings:      74
% 2.33/1.02  inst_num_of_non_proper_insts:           230
% 2.33/1.02  inst_num_of_duplicates:                 0
% 2.33/1.02  inst_inst_num_from_inst_to_res:         0
% 2.33/1.02  inst_dismatching_checking_time:         0.
% 2.33/1.02  
% 2.33/1.02  ------ Resolution
% 2.33/1.02  
% 2.33/1.02  res_num_of_clauses:                     0
% 2.33/1.02  res_num_in_passive:                     0
% 2.33/1.02  res_num_in_active:                      0
% 2.33/1.02  res_num_of_loops:                       148
% 2.33/1.02  res_forward_subset_subsumed:            63
% 2.33/1.02  res_backward_subset_subsumed:           0
% 2.33/1.02  res_forward_subsumed:                   0
% 2.33/1.02  res_backward_subsumed:                  3
% 2.33/1.02  res_forward_subsumption_resolution:     0
% 2.33/1.02  res_backward_subsumption_resolution:    0
% 2.33/1.02  res_clause_to_clause_subsumption:       1685
% 2.33/1.02  res_orphan_elimination:                 0
% 2.33/1.02  res_tautology_del:                      22
% 2.33/1.02  res_num_eq_res_simplified:              1
% 2.33/1.02  res_num_sel_changes:                    0
% 2.33/1.02  res_moves_from_active_to_pass:          0
% 2.33/1.02  
% 2.33/1.02  ------ Superposition
% 2.33/1.02  
% 2.33/1.02  sup_time_total:                         0.
% 2.33/1.02  sup_time_generating:                    0.
% 2.33/1.02  sup_time_sim_full:                      0.
% 2.33/1.02  sup_time_sim_immed:                     0.
% 2.33/1.02  
% 2.33/1.02  sup_num_of_clauses:                     38
% 2.33/1.02  sup_num_in_active:                      26
% 2.33/1.02  sup_num_in_passive:                     12
% 2.33/1.02  sup_num_of_loops:                       25
% 2.33/1.02  sup_fw_superposition:                   17
% 2.33/1.02  sup_bw_superposition:                   0
% 2.33/1.02  sup_immediate_simplified:               0
% 2.33/1.02  sup_given_eliminated:                   0
% 2.33/1.02  comparisons_done:                       0
% 2.33/1.02  comparisons_avoided:                    0
% 2.33/1.02  
% 2.33/1.02  ------ Simplifications
% 2.33/1.02  
% 2.33/1.02  
% 2.33/1.02  sim_fw_subset_subsumed:                 0
% 2.33/1.02  sim_bw_subset_subsumed:                 0
% 2.33/1.02  sim_fw_subsumed:                        0
% 2.33/1.02  sim_bw_subsumed:                        0
% 2.33/1.02  sim_fw_subsumption_res:                 1
% 2.33/1.02  sim_bw_subsumption_res:                 0
% 2.33/1.02  sim_tautology_del:                      0
% 2.33/1.02  sim_eq_tautology_del:                   2
% 2.33/1.02  sim_eq_res_simp:                        0
% 2.33/1.02  sim_fw_demodulated:                     0
% 2.33/1.02  sim_bw_demodulated:                     0
% 2.33/1.02  sim_light_normalised:                   3
% 2.33/1.02  sim_joinable_taut:                      0
% 2.33/1.02  sim_joinable_simp:                      0
% 2.33/1.02  sim_ac_normalised:                      0
% 2.33/1.02  sim_smt_subsumption:                    0
% 2.33/1.02  
%------------------------------------------------------------------------------
