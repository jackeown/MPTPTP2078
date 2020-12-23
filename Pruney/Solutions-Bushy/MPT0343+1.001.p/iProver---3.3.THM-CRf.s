%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0343+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:03 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 113 expanded)
%              Number of clauses        :   25 (  28 expanded)
%              Number of leaves         :    6 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  221 ( 675 expanded)
%              Number of equality atoms :   20 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( sK3 != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK3) )
              & ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK2 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK2)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK2) ) )
              | ~ m1_subset_1(X3,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( sK2 != sK3
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK3) )
          & ( r2_hidden(X3,sK3)
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f15,f14])).

fof(f25,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f11])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_8,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_737,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2,sK3),sK1)
    | r2_hidden(sK0(sK1,sK2,sK3),sK3)
    | ~ r2_hidden(sK0(sK1,sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_640,plain,
    ( ~ m1_subset_1(sK0(sK1,sK3,sK2),sK1)
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | r2_hidden(sK0(sK1,sK3,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X2,X0),X1)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_509,plain,
    ( m1_subset_1(sK0(X0,sK2,sK3),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_521,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_510,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r2_hidden(sK0(X0,sK2,sK3),sK2)
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_517,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK0(sK1,sK2,sK3),sK2)
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_511,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(X0,sK2,sK3),sK3)
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_513,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK0(sK1,sK2,sK3),sK3)
    | r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_427,plain,
    ( m1_subset_1(sK0(X0,sK3,sK2),X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_439,plain,
    ( m1_subset_1(sK0(sK1,sK3,sK2),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r2_hidden(sK0(X0,sK3,sK2),sK3)
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_435,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_428])).

cnf(c_429,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(X0,sK3,sK2),sK2)
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_431,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_409,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_737,c_640,c_521,c_517,c_513,c_439,c_435,c_431,c_409,c_6,c_9,c_10])).


%------------------------------------------------------------------------------
