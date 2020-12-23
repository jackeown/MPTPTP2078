%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0357+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:05 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 229 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,sK2),X1)
        & r1_tarski(k3_subset_1(X0,X1),sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
          & r1_tarski(k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13,f12])).

fof(f22,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_94,plain,
    ( r1_tarski(X0_35,X1_35)
    | ~ r1_tarski(k3_subset_1(X0_37,X1_35),k3_subset_1(X0_37,X0_35))
    | ~ m1_subset_1(X0_35,k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(X1_35,k1_zfmisc_1(X0_37)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_559,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_96,plain,
    ( ~ m1_subset_1(X0_35,k1_zfmisc_1(X0_37))
    | m1_subset_1(k3_subset_1(X0_37,X0_35),k1_zfmisc_1(X0_37)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_456,plain,
    ( m1_subset_1(k3_subset_1(X0_37,sK2),k1_zfmisc_1(X0_37))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_37)) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_458,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_102,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(X2_35,X3_35)
    | X2_35 != X0_35
    | X3_35 != X1_35 ),
    theory(equality)).

cnf(c_325,plain,
    ( r1_tarski(X0_35,X1_35)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | X0_35 != k3_subset_1(sK0,sK1)
    | X1_35 != sK2 ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_343,plain,
    ( r1_tarski(X0_35,k3_subset_1(X0_37,k3_subset_1(X0_37,sK2)))
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | X0_35 != k3_subset_1(sK0,sK1)
    | k3_subset_1(X0_37,k3_subset_1(X0_37,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_407,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(X0_37,k3_subset_1(X0_37,sK2)))
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | k3_subset_1(X0_37,k3_subset_1(X0_37,sK2)) != sK2
    | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_410,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) != sK2
    | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_95,plain,
    ( ~ m1_subset_1(X0_35,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,k3_subset_1(X0_37,X0_35)) = X0_35 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_344,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_37))
    | k3_subset_1(X0_37,k3_subset_1(X0_37,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_98,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_107,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_100,plain,
    ( X0_35 != X1_35
    | k3_subset_1(X0_37,X0_35) = k3_subset_1(X0_37,X1_35) ),
    theory(equality)).

cnf(c_103,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_559,c_458,c_410,c_350,c_107,c_103,c_4,c_5,c_6,c_7])).


%------------------------------------------------------------------------------
