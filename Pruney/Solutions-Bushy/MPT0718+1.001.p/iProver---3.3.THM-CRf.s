%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0718+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:58 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  271 ( 668 expanded)
%              Number of equality atoms :   22 (  76 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ~ v2_relat_1(sK3)
        & k1_relat_1(sK3) = k1_relat_1(X0)
        & v5_funct_1(X0,sK3)
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(sK2) = k1_relat_1(X1)
          & v5_funct_1(sK2,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ v2_relat_1(sK3)
    & k1_relat_1(sK2) = k1_relat_1(sK3)
    & v5_funct_1(sK2,sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f22,f21])).

fof(f36,plain,(
    k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK0(X0)))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK0(X0)))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f26,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | v1_xboole_0(k1_funct_1(X0,sK0(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ~ v2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    v5_funct_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | ~ v1_xboole_0(X1_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_741,plain,
    ( ~ r2_hidden(X0_41,k1_funct_1(X0_40,sK0(X0_40)))
    | ~ v1_xboole_0(k1_funct_1(X0_40,sK0(X0_40))) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_1182,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0(sK3)),k1_funct_1(sK3,sK0(sK3)))
    | ~ v1_xboole_0(k1_funct_1(sK3,sK0(sK3))) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_5,plain,
    ( ~ v5_funct_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_369,plain,
    ( ~ v5_funct_1(X0_40,X1_40)
    | ~ r2_hidden(X0_41,k1_relat_1(X0_40))
    | r2_hidden(k1_funct_1(X0_40,X0_41),k1_funct_1(X1_40,X0_41))
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X0_40)
    | ~ v1_funct_1(X1_40)
    | ~ v1_funct_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_814,plain,
    ( ~ v5_funct_1(sK2,X0_40)
    | ~ r2_hidden(X0_41,k1_relat_1(sK2))
    | r2_hidden(k1_funct_1(sK2,X0_41),k1_funct_1(X0_40,X0_41))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0_40)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_997,plain,
    ( ~ v5_funct_1(sK2,X0_40)
    | r2_hidden(k1_funct_1(sK2,sK0(sK3)),k1_funct_1(X0_40,sK0(sK3)))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK2))
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0_40)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_999,plain,
    ( ~ v5_funct_1(sK2,sK3)
    | r2_hidden(k1_funct_1(sK2,sK0(sK3)),k1_funct_1(sK3,sK0(sK3)))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_376,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_847,plain,
    ( sK0(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_380,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | r2_hidden(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_731,plain,
    ( r2_hidden(X0_41,X1_41)
    | ~ r2_hidden(sK0(X0_40),k1_relat_1(X0_40))
    | X1_41 != k1_relat_1(X0_40)
    | X0_41 != sK0(X0_40) ),
    inference(instantiation,[status(thm)],[c_380])).

cnf(c_760,plain,
    ( r2_hidden(X0_41,k1_relat_1(sK2))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | X0_41 != sK0(sK3)
    | k1_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_846,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | sK0(sK3) != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_8,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_366,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k1_funct_1(X0,sK0(X0)))
    | v2_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_37,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(k1_funct_1(sK3,sK0(sK3)))
    | v2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_34,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | v2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7,negated_conjecture,
    ( ~ v2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,negated_conjecture,
    ( v5_funct_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1182,c_999,c_847,c_846,c_366,c_37,c_34,c_7,c_9,c_10,c_11,c_12,c_13])).


%------------------------------------------------------------------------------
