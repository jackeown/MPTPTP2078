%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0917+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 31.91s
% Output     : CNFRefutation 31.91s
% Verified   : 
% Statistics : Number of formulae       :   25 (  50 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 162 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1563,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f335])).

fof(f1564,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1563])).

fof(f4345,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1564])).

fof(f1385,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1386,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    inference(negated_conjecture,[],[f1385])).

fof(f2793,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1386])).

fof(f2794,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2793])).

fof(f3869,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_zfmisc_1(sK431,sK433,sK435),k3_zfmisc_1(sK432,sK434,sK436))
      & r1_tarski(sK435,sK436)
      & r1_tarski(sK433,sK434)
      & r1_tarski(sK431,sK432) ) ),
    introduced(choice_axiom,[])).

fof(f3870,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK431,sK433,sK435),k3_zfmisc_1(sK432,sK434,sK436))
    & r1_tarski(sK435,sK436)
    & r1_tarski(sK433,sK434)
    & r1_tarski(sK431,sK432) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK431,sK432,sK433,sK434,sK435,sK436])],[f2794,f3869])).

fof(f6346,plain,(
    ~ r1_tarski(k3_zfmisc_1(sK431,sK433,sK435),k3_zfmisc_1(sK432,sK434,sK436)) ),
    inference(cnf_transformation,[],[f3870])).

fof(f1277,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6076,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1277])).

fof(f7240,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK431,sK433),sK435),k2_zfmisc_1(k2_zfmisc_1(sK432,sK434),sK436)) ),
    inference(definition_unfolding,[],[f6346,f6076,f6076])).

fof(f6345,plain,(
    r1_tarski(sK435,sK436) ),
    inference(cnf_transformation,[],[f3870])).

fof(f6344,plain,(
    r1_tarski(sK433,sK434) ),
    inference(cnf_transformation,[],[f3870])).

fof(f6343,plain,(
    r1_tarski(sK431,sK432) ),
    inference(cnf_transformation,[],[f3870])).

cnf(c_460,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f4345])).

cnf(c_113806,plain,
    ( r1_tarski(k2_zfmisc_1(sK431,sK433),k2_zfmisc_1(sK432,sK434))
    | ~ r1_tarski(sK433,sK434)
    | ~ r1_tarski(sK431,sK432) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_112043,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK431,sK433),sK435),k2_zfmisc_1(k2_zfmisc_1(sK432,sK434),sK436))
    | ~ r1_tarski(k2_zfmisc_1(sK431,sK433),k2_zfmisc_1(sK432,sK434))
    | ~ r1_tarski(sK435,sK436) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_2451,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK431,sK433),sK435),k2_zfmisc_1(k2_zfmisc_1(sK432,sK434),sK436)) ),
    inference(cnf_transformation,[],[f7240])).

cnf(c_2452,negated_conjecture,
    ( r1_tarski(sK435,sK436) ),
    inference(cnf_transformation,[],[f6345])).

cnf(c_2453,negated_conjecture,
    ( r1_tarski(sK433,sK434) ),
    inference(cnf_transformation,[],[f6344])).

cnf(c_2454,negated_conjecture,
    ( r1_tarski(sK431,sK432) ),
    inference(cnf_transformation,[],[f6343])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_113806,c_112043,c_2451,c_2452,c_2453,c_2454])).

%------------------------------------------------------------------------------
