%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:43 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 293 expanded)
%              Number of clauses        :   73 ( 109 expanded)
%              Number of leaves         :   12 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  310 (1051 expanded)
%              Number of equality atoms :  166 ( 567 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f57])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f40])).

fof(f59,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK5 != sK7
        | sK4 != sK6 )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( sK5 != sK7
      | sK4 != sK6 )
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f41,f59])).

fof(f103,plain,(
    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f25])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,
    ( sK5 != sK7
    | sK4 != sK6 ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1129,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,negated_conjecture,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_29,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1109,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6254,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_1109])).

cnf(c_12243,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_6254])).

cnf(c_14465,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK0(sK4,X1),sK6) = iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_12243])).

cnf(c_19209,plain,
    ( r2_hidden(sK0(sK4,X0),sK6) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(sK5,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_14465])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1130,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_35561,plain,
    ( r1_tarski(sK4,sK6) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19209,c_1130])).

cnf(c_35581,plain,
    ( r1_tarski(sK4,sK6) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_35561])).

cnf(c_28,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1110,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8645,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_1110])).

cnf(c_12244,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_8645])).

cnf(c_14741,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_12244])).

cnf(c_15067,plain,
    ( r2_hidden(sK0(sK5,X0),sK7) = iProver_top
    | r1_tarski(sK4,X1) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_14741])).

cnf(c_24321,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(sK5,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_15067,c_1130])).

cnf(c_24698,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(sK5,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_24321])).

cnf(c_635,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_631,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6126,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_635,c_631])).

cnf(c_18651,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK6,sK7),X0)
    | r1_tarski(k2_zfmisc_1(sK4,sK5),X0) ),
    inference(resolution,[status(thm)],[c_6126,c_37])).

cnf(c_32,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_18732,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,X0))
    | ~ r1_tarski(sK7,X0) ),
    inference(resolution,[status(thm)],[c_18651,c_32])).

cnf(c_31,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_18912,plain,
    ( r1_tarski(sK4,sK6)
    | ~ r1_tarski(sK7,sK5)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_18732,c_31])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_22,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_60,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_66,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_632,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1373,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1374,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_1106,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2070,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,X0)) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_1106])).

cnf(c_1107,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3041,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK4,sK6) = iProver_top
    | r1_tarski(sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_1107])).

cnf(c_3077,plain,
    ( r1_tarski(sK4,sK6)
    | ~ r1_tarski(sK7,sK5)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3041])).

cnf(c_22333,plain,
    ( ~ r1_tarski(sK7,sK5)
    | r1_tarski(sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18912,c_35,c_60,c_66,c_1374,c_3077])).

cnf(c_22334,plain,
    ( r1_tarski(sK4,sK6)
    | ~ r1_tarski(sK7,sK5) ),
    inference(renaming,[status(thm)],[c_22333])).

cnf(c_34,negated_conjecture,
    ( sK4 != sK6
    | sK5 != sK7 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1938,plain,
    ( ~ r1_tarski(sK6,sK4)
    | ~ r1_tarski(sK4,sK6)
    | sK5 != sK7 ),
    inference(resolution,[status(thm)],[c_18,c_34])).

cnf(c_2099,plain,
    ( ~ r1_tarski(sK6,sK4)
    | ~ r1_tarski(sK4,sK6)
    | ~ r1_tarski(sK7,sK5)
    | ~ r1_tarski(sK5,sK7) ),
    inference(resolution,[status(thm)],[c_1938,c_18])).

cnf(c_22742,plain,
    ( ~ r1_tarski(sK6,sK4)
    | ~ r1_tarski(sK7,sK5)
    | ~ r1_tarski(sK5,sK7) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_22334,c_2099])).

cnf(c_22744,plain,
    ( r1_tarski(sK6,sK4) != iProver_top
    | r1_tarski(sK7,sK5) != iProver_top
    | r1_tarski(sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22742])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1105,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1439,plain,
    ( r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_1105])).

cnf(c_30,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1108,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4252,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,sK6) != iProver_top
    | r1_tarski(sK7,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1108])).

cnf(c_2071,plain,
    ( r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK6,X0),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_1106])).

cnf(c_3042,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK6,sK4) = iProver_top
    | r1_tarski(sK5,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2071,c_1107])).

cnf(c_1836,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1839,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1836])).

cnf(c_1743,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1744,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1743])).

cnf(c_1539,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1545,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1539])).

cnf(c_1547,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_1522,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1528,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_1530,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_1375,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1376,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f104])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35581,c_24698,c_22744,c_4252,c_3042,c_1839,c_1744,c_1547,c_1530,c_1376,c_1374,c_66,c_60,c_35,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 37
% 7.75/1.50  conjectures                             4
% 7.75/1.50  EPR                                     10
% 7.75/1.50  Horn                                    27
% 7.75/1.50  unary                                   13
% 7.75/1.50  binary                                  13
% 7.75/1.50  lits                                    73
% 7.75/1.50  lits eq                                 19
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 2
% 7.75/1.50  fd_pseudo_cond                          5
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Input Options Time Limit: Unbounded
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f1,axiom,(
% 7.75/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f33,plain,(
% 7.75/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f1])).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.50    inference(nnf_transformation,[],[f33])).
% 7.75/1.50  
% 7.75/1.50  fof(f43,plain,(
% 7.75/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.50    inference(rectify,[],[f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f45])).
% 7.75/1.50  
% 7.75/1.50  fof(f24,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f57,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.75/1.50    inference(nnf_transformation,[],[f24])).
% 7.75/1.50  
% 7.75/1.50  fof(f58,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.75/1.50    inference(flattening,[],[f57])).
% 7.75/1.50  
% 7.75/1.50  fof(f98,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f58])).
% 7.75/1.50  
% 7.75/1.50  fof(f27,conjecture,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f28,negated_conjecture,(
% 7.75/1.50    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.75/1.50    inference(negated_conjecture,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.75/1.50    inference(ennf_transformation,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.75/1.50    inference(flattening,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f59,plain,(
% 7.75/1.50    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK5 != sK7 | sK4 != sK6) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f60,plain,(
% 7.75/1.50    (sK5 != sK7 | sK4 != sK6) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f41,f59])).
% 7.75/1.50  
% 7.75/1.50  fof(f103,plain,(
% 7.75/1.50    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f96,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f58])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f45])).
% 7.75/1.50  
% 7.75/1.50  fof(f97,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f58])).
% 7.75/1.50  
% 7.75/1.50  fof(f26,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 7.75/1.50    inference(ennf_transformation,[],[f26])).
% 7.75/1.50  
% 7.75/1.50  fof(f102,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f25,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 7.75/1.50    inference(ennf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f99,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 7.75/1.50    inference(cnf_transformation,[],[f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f105,plain,(
% 7.75/1.50    k1_xboole_0 != sK5),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f83,plain,(
% 7.75/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f8,axiom,(
% 7.75/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(nnf_transformation,[],[f8])).
% 7.75/1.50  
% 7.75/1.50  fof(f56,plain,(
% 7.75/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.50    inference(flattening,[],[f55])).
% 7.75/1.50  
% 7.75/1.50  fof(f80,plain,(
% 7.75/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f56])).
% 7.75/1.50  
% 7.75/1.50  fof(f106,plain,(
% 7.75/1.50    sK5 != sK7 | sK4 != sK6),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f101,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f100,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 7.75/1.50    inference(cnf_transformation,[],[f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f104,plain,(
% 7.75/1.50    k1_xboole_0 != sK4),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2,plain,
% 7.75/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1129,plain,
% 7.75/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.75/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_27,plain,
% 7.75/1.50      ( ~ r2_hidden(X0,X1)
% 7.75/1.50      | ~ r2_hidden(X2,X3)
% 7.75/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1111,plain,
% 7.75/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.75/1.50      | r2_hidden(X2,X3) != iProver_top
% 7.75/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_37,negated_conjecture,
% 7.75/1.50      ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK6,sK7) ),
% 7.75/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_29,plain,
% 7.75/1.50      ( r2_hidden(X0,X1)
% 7.75/1.50      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1109,plain,
% 7.75/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.75/1.50      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6254,plain,
% 7.75/1.50      ( r2_hidden(X0,sK6) = iProver_top
% 7.75/1.50      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_37,c_1109]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_12243,plain,
% 7.75/1.50      ( r2_hidden(X0,sK6) = iProver_top
% 7.75/1.50      | r2_hidden(X0,sK4) != iProver_top
% 7.75/1.50      | r2_hidden(X1,sK5) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1111,c_6254]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14465,plain,
% 7.75/1.50      ( r2_hidden(X0,sK5) != iProver_top
% 7.75/1.50      | r2_hidden(sK0(sK4,X1),sK6) = iProver_top
% 7.75/1.50      | r1_tarski(sK4,X1) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1129,c_12243]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19209,plain,
% 7.75/1.50      ( r2_hidden(sK0(sK4,X0),sK6) = iProver_top
% 7.75/1.50      | r1_tarski(sK4,X0) = iProver_top
% 7.75/1.50      | r1_tarski(sK5,X1) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1129,c_14465]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1,plain,
% 7.75/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1130,plain,
% 7.75/1.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.75/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_35561,plain,
% 7.75/1.50      ( r1_tarski(sK4,sK6) = iProver_top
% 7.75/1.50      | r1_tarski(sK5,X0) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_19209,c_1130]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_35581,plain,
% 7.75/1.50      ( r1_tarski(sK4,sK6) = iProver_top
% 7.75/1.50      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_35561]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_28,plain,
% 7.75/1.50      ( r2_hidden(X0,X1)
% 7.75/1.50      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1110,plain,
% 7.75/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.75/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8645,plain,
% 7.75/1.50      ( r2_hidden(X0,sK7) = iProver_top
% 7.75/1.50      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_37,c_1110]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_12244,plain,
% 7.75/1.50      ( r2_hidden(X0,sK4) != iProver_top
% 7.75/1.50      | r2_hidden(X1,sK7) = iProver_top
% 7.75/1.50      | r2_hidden(X1,sK5) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1111,c_8645]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_14741,plain,
% 7.75/1.50      ( r2_hidden(X0,sK7) = iProver_top
% 7.75/1.50      | r2_hidden(X0,sK5) != iProver_top
% 7.75/1.50      | r1_tarski(sK4,X1) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1129,c_12244]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_15067,plain,
% 7.75/1.50      ( r2_hidden(sK0(sK5,X0),sK7) = iProver_top
% 7.75/1.50      | r1_tarski(sK4,X1) = iProver_top
% 7.75/1.50      | r1_tarski(sK5,X0) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1129,c_14741]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24321,plain,
% 7.75/1.50      ( r1_tarski(sK4,X0) = iProver_top
% 7.75/1.50      | r1_tarski(sK5,sK7) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_15067,c_1130]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24698,plain,
% 7.75/1.50      ( r1_tarski(sK4,k1_xboole_0) = iProver_top
% 7.75/1.50      | r1_tarski(sK5,sK7) = iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_24321]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_635,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.75/1.50      theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_631,plain,( X0 = X0 ),theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6126,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_635,c_631]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18651,plain,
% 7.75/1.50      ( ~ r1_tarski(k2_zfmisc_1(sK6,sK7),X0)
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(sK4,sK5),X0) ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_6126,c_37]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_32,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1)
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18732,plain,
% 7.75/1.50      ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,X0))
% 7.75/1.50      | ~ r1_tarski(sK7,X0) ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_18651,c_32]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_31,plain,
% 7.75/1.50      ( r1_tarski(X0,X1)
% 7.75/1.50      | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
% 7.75/1.50      | k1_xboole_0 = X2 ),
% 7.75/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18912,plain,
% 7.75/1.50      ( r1_tarski(sK4,sK6) | ~ r1_tarski(sK7,sK5) | k1_xboole_0 = sK5 ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_18732,c_31]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_35,negated_conjecture,
% 7.75/1.50      ( k1_xboole_0 != sK5 ),
% 7.75/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22,plain,
% 7.75/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_60,plain,
% 7.75/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_22]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_66,plain,
% 7.75/1.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.75/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_632,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1373,plain,
% 7.75/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_632]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1374,plain,
% 7.75/1.50      ( sK5 != k1_xboole_0
% 7.75/1.50      | k1_xboole_0 = sK5
% 7.75/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1373]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1106,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2070,plain,
% 7.75/1.50      ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK6,X0)) = iProver_top
% 7.75/1.50      | r1_tarski(sK7,X0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_37,c_1106]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1107,plain,
% 7.75/1.50      ( k1_xboole_0 = X0
% 7.75/1.50      | r1_tarski(X1,X2) = iProver_top
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3041,plain,
% 7.75/1.50      ( sK5 = k1_xboole_0
% 7.75/1.50      | r1_tarski(sK4,sK6) = iProver_top
% 7.75/1.50      | r1_tarski(sK7,sK5) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2070,c_1107]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3077,plain,
% 7.75/1.50      ( r1_tarski(sK4,sK6) | ~ r1_tarski(sK7,sK5) | sK5 = k1_xboole_0 ),
% 7.75/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_3041]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22333,plain,
% 7.75/1.50      ( ~ r1_tarski(sK7,sK5) | r1_tarski(sK4,sK6) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_18912,c_35,c_60,c_66,c_1374,c_3077]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22334,plain,
% 7.75/1.50      ( r1_tarski(sK4,sK6) | ~ r1_tarski(sK7,sK5) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_22333]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_34,negated_conjecture,
% 7.75/1.50      ( sK4 != sK6 | sK5 != sK7 ),
% 7.75/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1938,plain,
% 7.75/1.50      ( ~ r1_tarski(sK6,sK4) | ~ r1_tarski(sK4,sK6) | sK5 != sK7 ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_18,c_34]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2099,plain,
% 7.75/1.50      ( ~ r1_tarski(sK6,sK4)
% 7.75/1.50      | ~ r1_tarski(sK4,sK6)
% 7.75/1.50      | ~ r1_tarski(sK7,sK5)
% 7.75/1.50      | ~ r1_tarski(sK5,sK7) ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_1938,c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22742,plain,
% 7.75/1.50      ( ~ r1_tarski(sK6,sK4)
% 7.75/1.50      | ~ r1_tarski(sK7,sK5)
% 7.75/1.50      | ~ r1_tarski(sK5,sK7) ),
% 7.75/1.50      inference(backward_subsumption_resolution,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_22334,c_2099]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_22744,plain,
% 7.75/1.50      ( r1_tarski(sK6,sK4) != iProver_top
% 7.75/1.50      | r1_tarski(sK7,sK5) != iProver_top
% 7.75/1.50      | r1_tarski(sK5,sK7) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_22742]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_33,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1)
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1105,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1439,plain,
% 7.75/1.50      ( r1_tarski(X0,sK6) != iProver_top
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(X0,sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_37,c_1105]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_30,plain,
% 7.75/1.50      ( r1_tarski(X0,X1)
% 7.75/1.50      | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
% 7.75/1.50      | k1_xboole_0 = X2 ),
% 7.75/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1108,plain,
% 7.75/1.50      ( k1_xboole_0 = X0
% 7.75/1.50      | r1_tarski(X1,X2) = iProver_top
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4252,plain,
% 7.75/1.50      ( sK4 = k1_xboole_0
% 7.75/1.50      | r1_tarski(sK4,sK6) != iProver_top
% 7.75/1.50      | r1_tarski(sK7,sK5) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_1439,c_1108]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2071,plain,
% 7.75/1.50      ( r1_tarski(X0,sK7) != iProver_top
% 7.75/1.50      | r1_tarski(k2_zfmisc_1(sK6,X0),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_37,c_1106]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3042,plain,
% 7.75/1.50      ( sK5 = k1_xboole_0
% 7.75/1.50      | r1_tarski(sK6,sK4) = iProver_top
% 7.75/1.50      | r1_tarski(sK5,sK7) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2071,c_1107]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1836,plain,
% 7.75/1.50      ( r1_tarski(k1_xboole_0,sK5) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_22]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1839,plain,
% 7.75/1.50      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1836]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1743,plain,
% 7.75/1.50      ( r1_tarski(k1_xboole_0,sK4) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_22]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1744,plain,
% 7.75/1.50      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1743]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1539,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1545,plain,
% 7.75/1.50      ( sK4 = X0
% 7.75/1.50      | r1_tarski(X0,sK4) != iProver_top
% 7.75/1.50      | r1_tarski(sK4,X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1539]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1547,plain,
% 7.75/1.50      ( sK4 = k1_xboole_0
% 7.75/1.50      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 7.75/1.50      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1545]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1522,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1528,plain,
% 7.75/1.50      ( sK5 = X0
% 7.75/1.50      | r1_tarski(X0,sK5) != iProver_top
% 7.75/1.50      | r1_tarski(sK5,X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1530,plain,
% 7.75/1.50      ( sK5 = k1_xboole_0
% 7.75/1.50      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 7.75/1.50      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1528]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1375,plain,
% 7.75/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_632]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1376,plain,
% 7.75/1.50      ( sK4 != k1_xboole_0
% 7.75/1.50      | k1_xboole_0 = sK4
% 7.75/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_1375]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_36,negated_conjecture,
% 7.75/1.50      ( k1_xboole_0 != sK4 ),
% 7.75/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(contradiction,plain,
% 7.75/1.50      ( $false ),
% 7.75/1.50      inference(minisat,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_35581,c_24698,c_22744,c_4252,c_3042,c_1839,c_1744,
% 7.75/1.50                 c_1547,c_1530,c_1376,c_1374,c_66,c_60,c_35,c_36]) ).
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  ------                               Statistics
% 7.75/1.50  
% 7.75/1.50  ------ Selected
% 7.75/1.50  
% 7.75/1.50  total_time:                             0.896
% 7.75/1.50  
%------------------------------------------------------------------------------
