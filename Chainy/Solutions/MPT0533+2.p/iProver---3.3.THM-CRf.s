%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0533+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 23.38s
% Output     : CNFRefutation 23.38s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  150 ( 322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f707,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1293,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f1294,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1293])).

fof(f2945,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1294])).

fof(f708,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1295,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f1296,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1295])).

fof(f2946,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1296])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1218,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2835,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1218])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1741,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2796,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1741])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f836,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f837,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f836])).

fof(f1949,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f837])).

fof(f709,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f710,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f709])).

fof(f1297,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f710])).

fof(f1298,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1297])).

fof(f1812,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK154))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK154)
        & v1_relat_1(sK154) ) ) ),
    introduced(choice_axiom,[])).

fof(f1811,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,X3))
          & r1_tarski(sK151,sK152)
          & r1_tarski(sK153,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK153) ) ),
    introduced(choice_axiom,[])).

fof(f1813,plain,
    ( ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK154))
    & r1_tarski(sK151,sK152)
    & r1_tarski(sK153,sK154)
    & v1_relat_1(sK154)
    & v1_relat_1(sK153) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151,sK152,sK153,sK154])],[f1298,f1812,f1811])).

fof(f2951,plain,(
    ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK154)) ),
    inference(cnf_transformation,[],[f1813])).

fof(f2950,plain,(
    r1_tarski(sK151,sK152) ),
    inference(cnf_transformation,[],[f1813])).

fof(f2949,plain,(
    r1_tarski(sK153,sK154) ),
    inference(cnf_transformation,[],[f1813])).

fof(f2948,plain,(
    v1_relat_1(sK154) ),
    inference(cnf_transformation,[],[f1813])).

fof(f2947,plain,(
    v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f1813])).

cnf(c_1101,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2945])).

cnf(c_55000,plain,
    ( r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(X0,sK153))
    | ~ r1_tarski(sK151,X0)
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_80206,plain,
    ( r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153))
    | ~ r1_tarski(sK151,sK152)
    | ~ v1_relat_1(sK153) ),
    inference(instantiation,[status(thm)],[c_55000])).

cnf(c_1102,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2946])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2835])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2796])).

cnf(c_9439,plain,
    ( r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_991,c_951])).

cnf(c_9440,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_9439])).

cnf(c_80018,plain,
    ( r1_tarski(k8_relat_1(sK152,sK153),k8_relat_1(sK152,sK154))
    | ~ r1_tarski(sK153,sK154)
    | ~ v1_relat_1(sK154) ),
    inference(instantiation,[status(thm)],[c_9440])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1949])).

cnf(c_41741,plain,
    ( ~ r1_tarski(X0,k8_relat_1(sK152,sK154))
    | ~ r1_tarski(k8_relat_1(sK151,sK153),X0)
    | r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK154)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_54999,plain,
    ( ~ r1_tarski(k8_relat_1(X0,sK153),k8_relat_1(sK152,sK154))
    | ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(X0,sK153))
    | r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK154)) ),
    inference(instantiation,[status(thm)],[c_41741])).

cnf(c_80017,plain,
    ( ~ r1_tarski(k8_relat_1(sK152,sK153),k8_relat_1(sK152,sK154))
    | r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK154))
    | ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK153)) ),
    inference(instantiation,[status(thm)],[c_54999])).

cnf(c_1103,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK151,sK153),k8_relat_1(sK152,sK154)) ),
    inference(cnf_transformation,[],[f2951])).

cnf(c_1104,negated_conjecture,
    ( r1_tarski(sK151,sK152) ),
    inference(cnf_transformation,[],[f2950])).

cnf(c_1105,negated_conjecture,
    ( r1_tarski(sK153,sK154) ),
    inference(cnf_transformation,[],[f2949])).

cnf(c_1106,negated_conjecture,
    ( v1_relat_1(sK154) ),
    inference(cnf_transformation,[],[f2948])).

cnf(c_1107,negated_conjecture,
    ( v1_relat_1(sK153) ),
    inference(cnf_transformation,[],[f2947])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_80206,c_80018,c_80017,c_1103,c_1104,c_1105,c_1106,c_1107])).

%------------------------------------------------------------------------------
