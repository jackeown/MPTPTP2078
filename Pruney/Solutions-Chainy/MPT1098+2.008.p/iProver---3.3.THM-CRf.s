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
% DateTime   : Thu Dec  3 12:10:42 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 110 expanded)
%              Number of clauses        :   39 (  41 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  220 ( 466 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK3,k2_zfmisc_1(X3,sK5))
          | ~ r1_tarski(X3,sK4)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
      & v1_finset_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK3,k2_zfmisc_1(X3,sK5))
        | ~ r1_tarski(X3,sK4)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
    & v1_finset_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f9,f16])).

fof(f30,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK3,k2_zfmisc_1(X3,sK5))
      | ~ r1_tarski(X3,sK4)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2)))
        & r1_tarski(sK2(X0,X1,X2),X2)
        & v1_finset_1(sK2(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X1)
        & v1_finset_1(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2)))
        & r1_tarski(sK2(X0,X1,X2),X2)
        & v1_finset_1(sK2(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X1)
        & v1_finset_1(sK1(X0,X1,X2)) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X2),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X1)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK1(X0,X1,X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    v1_finset_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_125,plain,
    ( ~ r2_hidden(sK0(X0_38,X1_38),X1_38)
    | r1_tarski(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_9820,plain,
    ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,sK5))
    | r1_tarski(sK3,k2_zfmisc_1(X0_38,sK5)) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_19200,plain,
    ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5))
    | r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
    inference(instantiation,[status(thm)],[c_9820])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK5))
    | ~ v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_115,negated_conjecture,
    ( ~ r1_tarski(X0_38,sK4)
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0_38,sK5))
    | ~ v1_finset_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_18539,plain,
    ( ~ r1_tarski(sK1(sK3,sK4,sK5),sK4)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5))
    | ~ v1_finset_1(sK1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k2_zfmisc_1(X2_38,X0_38),k2_zfmisc_1(X2_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_11656,plain,
    ( ~ r1_tarski(sK2(sK3,sK4,sK5),X0_38)
    | r1_tarski(k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),X0_38)) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_13578,plain,
    ( ~ r1_tarski(sK2(sK3,sK4,sK5),sK5)
    | r1_tarski(k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
    inference(instantiation,[status(thm)],[c_11656])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_123,plain,
    ( ~ r2_hidden(X0_39,X0_38)
    | r2_hidden(X0_39,X1_38)
    | ~ r1_tarski(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_10038,plain,
    ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X1_38)
    | r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X2_38)
    | ~ r1_tarski(X1_38,X2_38) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_10298,plain,
    ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X1_38)
    | r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,sK5))
    | ~ r1_tarski(X1_38,k2_zfmisc_1(X0_38,sK5)) ),
    inference(instantiation,[status(thm)],[c_10038])).

cnf(c_10325,plain,
    ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,X1_38))
    | r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,sK5))
    | ~ r1_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,sK5)) ),
    inference(instantiation,[status(thm)],[c_10298])).

cnf(c_10724,plain,
    ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)))
    | r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5))
    | ~ r1_tarski(k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
    inference(instantiation,[status(thm)],[c_10325])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_124,plain,
    ( r2_hidden(sK0(X0_38,X1_38),X0_38)
    | r1_tarski(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9821,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),sK3)
    | r1_tarski(sK3,k2_zfmisc_1(X0_38,sK5)) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_10698,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),sK3)
    | r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
    inference(instantiation,[status(thm)],[c_9821])).

cnf(c_9937,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X1_38)
    | ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),sK3)
    | ~ r1_tarski(sK3,X1_38) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_10364,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,X1_38))
    | ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),sK3)
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0_38,X1_38)) ),
    inference(instantiation,[status(thm)],[c_9937])).

cnf(c_10616,plain,
    ( r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)))
    | ~ r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),sK3)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_10364])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2)))
    | ~ v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_120,plain,
    ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
    | r1_tarski(X0_38,k2_zfmisc_1(sK1(X0_38,X1_38,X2_38),sK2(X0_38,X1_38,X2_38)))
    | ~ v1_finset_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_9921,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
    | ~ v1_finset_1(sK3) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(sK2(X0,X1,X2),X2)
    | ~ v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
    | r1_tarski(sK2(X0_38,X1_38,X2_38),X2_38)
    | ~ v1_finset_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_9905,plain,
    ( r1_tarski(sK2(sK3,sK4,sK5),sK5)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
    | ~ v1_finset_1(sK3) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_117,plain,
    ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
    | r1_tarski(sK1(X0_38,X1_38,X2_38),X1_38)
    | ~ v1_finset_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_9889,plain,
    ( r1_tarski(sK1(sK3,sK4,sK5),sK4)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
    | ~ v1_finset_1(sK3) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ v1_finset_1(X0)
    | v1_finset_1(sK1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_116,plain,
    ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
    | ~ v1_finset_1(X0_38)
    | v1_finset_1(sK1(X0_38,X1_38,X2_38)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_9829,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
    | v1_finset_1(sK1(sK3,sK4,sK5))
    | ~ v1_finset_1(sK3) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK3,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( v1_finset_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19200,c_18539,c_13578,c_10724,c_10698,c_10616,c_9921,c_9905,c_9889,c_9829,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:28:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.65/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.49  
% 7.65/1.49  ------  iProver source info
% 7.65/1.49  
% 7.65/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.49  git: non_committed_changes: false
% 7.65/1.49  git: last_make_outside_of_git: false
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  ------ Parsing...
% 7.65/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.49  ------ Proving...
% 7.65/1.49  ------ Problem Properties 
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  clauses                                 13
% 7.65/1.49  conjectures                             3
% 7.65/1.49  EPR                                     2
% 7.65/1.49  Horn                                    12
% 7.65/1.49  unary                                   2
% 7.65/1.49  binary                                  4
% 7.65/1.49  lits                                    31
% 7.65/1.49  lits eq                                 0
% 7.65/1.49  fd_pure                                 0
% 7.65/1.49  fd_pseudo                               0
% 7.65/1.49  fd_cond                                 0
% 7.65/1.49  fd_pseudo_cond                          0
% 7.65/1.49  AC symbols                              0
% 7.65/1.49  
% 7.65/1.49  ------ Input Options Time Limit: Unbounded
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing...
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.65/1.49  Current options:
% 7.65/1.49  ------ 
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing...
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  % SZS status Theorem for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  fof(f1,axiom,(
% 7.65/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.65/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f6,plain,(
% 7.65/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.65/1.49    inference(ennf_transformation,[],[f1])).
% 7.65/1.49  
% 7.65/1.49  fof(f10,plain,(
% 7.65/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.65/1.49    inference(nnf_transformation,[],[f6])).
% 7.65/1.49  
% 7.65/1.49  fof(f11,plain,(
% 7.65/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.65/1.49    inference(rectify,[],[f10])).
% 7.65/1.49  
% 7.65/1.49  fof(f12,plain,(
% 7.65/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f13,plain,(
% 7.65/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.65/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 7.65/1.49  
% 7.65/1.49  fof(f20,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f13])).
% 7.65/1.49  
% 7.65/1.49  fof(f4,conjecture,(
% 7.65/1.49    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 7.65/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f5,negated_conjecture,(
% 7.65/1.49    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 7.65/1.49    inference(negated_conjecture,[],[f4])).
% 7.65/1.49  
% 7.65/1.49  fof(f9,plain,(
% 7.65/1.49    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 7.65/1.49    inference(ennf_transformation,[],[f5])).
% 7.65/1.49  
% 7.65/1.49  fof(f16,plain,(
% 7.65/1.49    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0)) => (! [X3] : (~r1_tarski(sK3,k2_zfmisc_1(X3,sK5)) | ~r1_tarski(X3,sK4) | ~v1_finset_1(X3)) & r1_tarski(sK3,k2_zfmisc_1(sK4,sK5)) & v1_finset_1(sK3))),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f17,plain,(
% 7.65/1.49    ! [X3] : (~r1_tarski(sK3,k2_zfmisc_1(X3,sK5)) | ~r1_tarski(X3,sK4) | ~v1_finset_1(X3)) & r1_tarski(sK3,k2_zfmisc_1(sK4,sK5)) & v1_finset_1(sK3)),
% 7.65/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f9,f16])).
% 7.65/1.49  
% 7.65/1.49  fof(f30,plain,(
% 7.65/1.49    ( ! [X3] : (~r1_tarski(sK3,k2_zfmisc_1(X3,sK5)) | ~r1_tarski(X3,sK4) | ~v1_finset_1(X3)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f17])).
% 7.65/1.49  
% 7.65/1.49  fof(f2,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 7.65/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f7,plain,(
% 7.65/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 7.65/1.49    inference(ennf_transformation,[],[f2])).
% 7.65/1.49  
% 7.65/1.49  fof(f22,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f7])).
% 7.65/1.49  
% 7.65/1.49  fof(f18,plain,(
% 7.65/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f13])).
% 7.65/1.49  
% 7.65/1.49  fof(f19,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f13])).
% 7.65/1.49  
% 7.65/1.49  fof(f3,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 7.65/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f8,plain,(
% 7.65/1.49    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 7.65/1.49    inference(ennf_transformation,[],[f3])).
% 7.65/1.49  
% 7.65/1.49  fof(f14,plain,(
% 7.65/1.49    ! [X2,X1,X0] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) => (r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2))) & r1_tarski(sK2(X0,X1,X2),X2) & v1_finset_1(sK2(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X1) & v1_finset_1(sK1(X0,X1,X2))))),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f15,plain,(
% 7.65/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2))) & r1_tarski(sK2(X0,X1,X2),X2) & v1_finset_1(sK2(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X1) & v1_finset_1(sK1(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 7.65/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f14])).
% 7.65/1.49  
% 7.65/1.49  fof(f27,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f15])).
% 7.65/1.49  
% 7.65/1.49  fof(f26,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (r1_tarski(sK2(X0,X1,X2),X2) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f15])).
% 7.65/1.49  
% 7.65/1.49  fof(f24,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X1) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f15])).
% 7.65/1.49  
% 7.65/1.49  fof(f23,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (v1_finset_1(sK1(X0,X1,X2)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f15])).
% 7.65/1.49  
% 7.65/1.49  fof(f29,plain,(
% 7.65/1.49    r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))),
% 7.65/1.49    inference(cnf_transformation,[],[f17])).
% 7.65/1.49  
% 7.65/1.49  fof(f28,plain,(
% 7.65/1.49    v1_finset_1(sK3)),
% 7.65/1.49    inference(cnf_transformation,[],[f17])).
% 7.65/1.49  
% 7.65/1.49  cnf(c_0,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.65/1.49      inference(cnf_transformation,[],[f20]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_125,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(X0_38,X1_38),X1_38) | r1_tarski(X0_38,X1_38) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9820,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,sK5))
% 7.65/1.49      | r1_tarski(sK3,k2_zfmisc_1(X0_38,sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_125]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_19200,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5))
% 7.65/1.49      | r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_9820]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10,negated_conjecture,
% 7.65/1.49      ( ~ r1_tarski(X0,sK4)
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK5))
% 7.65/1.49      | ~ v1_finset_1(X0) ),
% 7.65/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_115,negated_conjecture,
% 7.65/1.49      ( ~ r1_tarski(X0_38,sK4)
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(X0_38,sK5))
% 7.65/1.49      | ~ v1_finset_1(X0_38) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_18539,plain,
% 7.65/1.49      ( ~ r1_tarski(sK1(sK3,sK4,sK5),sK4)
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5))
% 7.65/1.49      | ~ v1_finset_1(sK1(sK3,sK4,sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_115]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_3,plain,
% 7.65/1.49      ( ~ r1_tarski(X0,X1)
% 7.65/1.49      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 7.65/1.49      inference(cnf_transformation,[],[f22]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_122,plain,
% 7.65/1.49      ( ~ r1_tarski(X0_38,X1_38)
% 7.65/1.49      | r1_tarski(k2_zfmisc_1(X2_38,X0_38),k2_zfmisc_1(X2_38,X1_38)) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_11656,plain,
% 7.65/1.49      ( ~ r1_tarski(sK2(sK3,sK4,sK5),X0_38)
% 7.65/1.49      | r1_tarski(k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),X0_38)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_122]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_13578,plain,
% 7.65/1.49      ( ~ r1_tarski(sK2(sK3,sK4,sK5),sK5)
% 7.65/1.49      | r1_tarski(k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_11656]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_2,plain,
% 7.65/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.65/1.49      inference(cnf_transformation,[],[f18]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_123,plain,
% 7.65/1.49      ( ~ r2_hidden(X0_39,X0_38)
% 7.65/1.49      | r2_hidden(X0_39,X1_38)
% 7.65/1.49      | ~ r1_tarski(X0_38,X1_38) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10038,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X1_38)
% 7.65/1.49      | r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X2_38)
% 7.65/1.49      | ~ r1_tarski(X1_38,X2_38) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_123]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10298,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X1_38)
% 7.65/1.49      | r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,sK5))
% 7.65/1.49      | ~ r1_tarski(X1_38,k2_zfmisc_1(X0_38,sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_10038]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10325,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,X1_38))
% 7.65/1.49      | r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,sK5))
% 7.65/1.49      | ~ r1_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_10298]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10724,plain,
% 7.65/1.49      ( ~ r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)))
% 7.65/1.49      | r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5))
% 7.65/1.49      | ~ r1_tarski(k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_10325]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_1,plain,
% 7.65/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.65/1.49      inference(cnf_transformation,[],[f19]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_124,plain,
% 7.65/1.49      ( r2_hidden(sK0(X0_38,X1_38),X0_38) | r1_tarski(X0_38,X1_38) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9821,plain,
% 7.65/1.49      ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),sK3)
% 7.65/1.49      | r1_tarski(sK3,k2_zfmisc_1(X0_38,sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_124]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10698,plain,
% 7.65/1.49      ( r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),sK3)
% 7.65/1.49      | r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_9821]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9937,plain,
% 7.65/1.49      ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),X1_38)
% 7.65/1.49      | ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),sK3)
% 7.65/1.49      | ~ r1_tarski(sK3,X1_38) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_123]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10364,plain,
% 7.65/1.49      ( r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),k2_zfmisc_1(X0_38,X1_38))
% 7.65/1.49      | ~ r2_hidden(sK0(sK3,k2_zfmisc_1(X0_38,sK5)),sK3)
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(X0_38,X1_38)) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_9937]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_10616,plain,
% 7.65/1.49      ( r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)))
% 7.65/1.49      | ~ r2_hidden(sK0(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK5)),sK3)
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5))) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_10364]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_5,plain,
% 7.65/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.65/1.49      | r1_tarski(X0,k2_zfmisc_1(sK1(X0,X1,X2),sK2(X0,X1,X2)))
% 7.65/1.49      | ~ v1_finset_1(X0) ),
% 7.65/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_120,plain,
% 7.65/1.49      ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
% 7.65/1.49      | r1_tarski(X0_38,k2_zfmisc_1(sK1(X0_38,X1_38,X2_38),sK2(X0_38,X1_38,X2_38)))
% 7.65/1.49      | ~ v1_finset_1(X0_38) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9921,plain,
% 7.65/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK1(sK3,sK4,sK5),sK2(sK3,sK4,sK5)))
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
% 7.65/1.49      | ~ v1_finset_1(sK3) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_120]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_6,plain,
% 7.65/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.65/1.49      | r1_tarski(sK2(X0,X1,X2),X2)
% 7.65/1.49      | ~ v1_finset_1(X0) ),
% 7.65/1.49      inference(cnf_transformation,[],[f26]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_119,plain,
% 7.65/1.49      ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
% 7.65/1.49      | r1_tarski(sK2(X0_38,X1_38,X2_38),X2_38)
% 7.65/1.49      | ~ v1_finset_1(X0_38) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9905,plain,
% 7.65/1.49      ( r1_tarski(sK2(sK3,sK4,sK5),sK5)
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
% 7.65/1.49      | ~ v1_finset_1(sK3) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_119]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_8,plain,
% 7.65/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.65/1.49      | r1_tarski(sK1(X0,X1,X2),X1)
% 7.65/1.49      | ~ v1_finset_1(X0) ),
% 7.65/1.49      inference(cnf_transformation,[],[f24]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_117,plain,
% 7.65/1.49      ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
% 7.65/1.49      | r1_tarski(sK1(X0_38,X1_38,X2_38),X1_38)
% 7.65/1.49      | ~ v1_finset_1(X0_38) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9889,plain,
% 7.65/1.49      ( r1_tarski(sK1(sK3,sK4,sK5),sK4)
% 7.65/1.49      | ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
% 7.65/1.49      | ~ v1_finset_1(sK3) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_117]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9,plain,
% 7.65/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.65/1.49      | ~ v1_finset_1(X0)
% 7.65/1.49      | v1_finset_1(sK1(X0,X1,X2)) ),
% 7.65/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_116,plain,
% 7.65/1.49      ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
% 7.65/1.49      | ~ v1_finset_1(X0_38)
% 7.65/1.49      | v1_finset_1(sK1(X0_38,X1_38,X2_38)) ),
% 7.65/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_9829,plain,
% 7.65/1.49      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK4,sK5))
% 7.65/1.49      | v1_finset_1(sK1(sK3,sK4,sK5))
% 7.65/1.49      | ~ v1_finset_1(sK3) ),
% 7.65/1.49      inference(instantiation,[status(thm)],[c_116]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_11,negated_conjecture,
% 7.65/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK4,sK5)) ),
% 7.65/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(c_12,negated_conjecture,
% 7.65/1.49      ( v1_finset_1(sK3) ),
% 7.65/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.65/1.49  
% 7.65/1.49  cnf(contradiction,plain,
% 7.65/1.49      ( $false ),
% 7.65/1.49      inference(minisat,
% 7.65/1.49                [status(thm)],
% 7.65/1.49                [c_19200,c_18539,c_13578,c_10724,c_10698,c_10616,c_9921,
% 7.65/1.49                 c_9905,c_9889,c_9829,c_11,c_12]) ).
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  ------                               Statistics
% 7.65/1.49  
% 7.65/1.49  ------ Selected
% 7.65/1.49  
% 7.65/1.49  total_time:                             0.759
% 7.65/1.49  
%------------------------------------------------------------------------------
