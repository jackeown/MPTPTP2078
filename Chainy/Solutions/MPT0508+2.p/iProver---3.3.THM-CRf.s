%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0508+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 23.36s
% Output     : CNFRefutation 23.36s
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
fof(f678,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1227,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f678])).

fof(f1228,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1227])).

fof(f2834,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1228])).

fof(f679,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1229,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f679])).

fof(f1230,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1229])).

fof(f2835,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1230])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1189,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f2762,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1189])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1675,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f2723,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1675])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f807,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f808,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f807])).

fof(f1876,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f808])).

fof(f680,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f681,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f680])).

fof(f1231,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f681])).

fof(f1232,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1231])).

fof(f1739,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(sK152,X1))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK152)
        & v1_relat_1(sK152) ) ) ),
    introduced(choice_axiom,[])).

fof(f1738,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(X3,sK150))
          & r1_tarski(sK149,sK150)
          & r1_tarski(sK151,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK151) ) ),
    introduced(choice_axiom,[])).

fof(f1740,plain,
    ( ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK152,sK150))
    & r1_tarski(sK149,sK150)
    & r1_tarski(sK151,sK152)
    & v1_relat_1(sK152)
    & v1_relat_1(sK151) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149,sK150,sK151,sK152])],[f1232,f1739,f1738])).

fof(f2840,plain,(
    ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK152,sK150)) ),
    inference(cnf_transformation,[],[f1740])).

fof(f2839,plain,(
    r1_tarski(sK149,sK150) ),
    inference(cnf_transformation,[],[f1740])).

fof(f2838,plain,(
    r1_tarski(sK151,sK152) ),
    inference(cnf_transformation,[],[f1740])).

fof(f2837,plain,(
    v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f1740])).

fof(f2836,plain,(
    v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f1740])).

cnf(c_1063,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f2834])).

cnf(c_53331,plain,
    ( r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,X0))
    | ~ r1_tarski(sK149,X0)
    | ~ v1_relat_1(sK151) ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_78897,plain,
    ( r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150))
    | ~ r1_tarski(sK149,sK150)
    | ~ v1_relat_1(sK151) ),
    inference(instantiation,[status(thm)],[c_53331])).

cnf(c_1064,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2835])).

cnf(c_991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2762])).

cnf(c_951,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2723])).

cnf(c_9094,plain,
    ( r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_991,c_951])).

cnf(c_9095,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_9094])).

cnf(c_78724,plain,
    ( r1_tarski(k7_relat_1(sK151,sK150),k7_relat_1(sK152,sK150))
    | ~ r1_tarski(sK151,sK152)
    | ~ v1_relat_1(sK152) ),
    inference(instantiation,[status(thm)],[c_9095])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1876])).

cnf(c_40192,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK152,sK150))
    | ~ r1_tarski(k7_relat_1(sK151,sK149),X0)
    | r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK152,sK150)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_53330,plain,
    ( ~ r1_tarski(k7_relat_1(sK151,X0),k7_relat_1(sK152,sK150))
    | r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK152,sK150))
    | ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,X0)) ),
    inference(instantiation,[status(thm)],[c_40192])).

cnf(c_78723,plain,
    ( ~ r1_tarski(k7_relat_1(sK151,sK150),k7_relat_1(sK152,sK150))
    | r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK152,sK150))
    | ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK151,sK150)) ),
    inference(instantiation,[status(thm)],[c_53330])).

cnf(c_1065,negated_conjecture,
    ( ~ r1_tarski(k7_relat_1(sK151,sK149),k7_relat_1(sK152,sK150)) ),
    inference(cnf_transformation,[],[f2840])).

cnf(c_1066,negated_conjecture,
    ( r1_tarski(sK149,sK150) ),
    inference(cnf_transformation,[],[f2839])).

cnf(c_1067,negated_conjecture,
    ( r1_tarski(sK151,sK152) ),
    inference(cnf_transformation,[],[f2838])).

cnf(c_1068,negated_conjecture,
    ( v1_relat_1(sK152) ),
    inference(cnf_transformation,[],[f2837])).

cnf(c_1069,negated_conjecture,
    ( v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f2836])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78897,c_78724,c_78723,c_1065,c_1066,c_1067,c_1068,c_1069])).

%------------------------------------------------------------------------------
