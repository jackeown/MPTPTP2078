%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0754+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 23.55s
% Output     : CNFRefutation 23.55s
% Verified   : 
% Statistics : Number of formulae       :   27 (  62 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  126 ( 521 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f823,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1769,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f823])).

fof(f1770,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1769])).

fof(f4152,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1770])).

fof(f1106,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1107,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X1)
              & v1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1106])).

fof(f2179,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1107])).

fof(f2180,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2179])).

fof(f2883,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ( ~ v5_ordinal1(sK255)
          | ~ v1_funct_1(sK255)
          | ~ v5_relat_1(sK255,X1)
          | ~ v1_relat_1(sK255) )
        & v5_ordinal1(sK255)
        & v1_funct_1(sK255)
        & v5_relat_1(sK255,X0)
        & v1_relat_1(sK255) ) ) ),
    introduced(choice_axiom,[])).

fof(f2882,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(X2)
              | ~ v1_funct_1(X2)
              | ~ v5_relat_1(X2,X1)
              | ~ v1_relat_1(X2) )
            & v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,sK254)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,sK253)
          & v1_relat_1(X2) )
      & r1_tarski(sK253,sK254) ) ),
    introduced(choice_axiom,[])).

fof(f2884,plain,
    ( ( ~ v5_ordinal1(sK255)
      | ~ v1_funct_1(sK255)
      | ~ v5_relat_1(sK255,sK254)
      | ~ v1_relat_1(sK255) )
    & v5_ordinal1(sK255)
    & v1_funct_1(sK255)
    & v5_relat_1(sK255,sK253)
    & v1_relat_1(sK255)
    & r1_tarski(sK253,sK254) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK253,sK254,sK255])],[f2180,f2883,f2882])).

fof(f4706,plain,
    ( ~ v5_ordinal1(sK255)
    | ~ v1_funct_1(sK255)
    | ~ v5_relat_1(sK255,sK254)
    | ~ v1_relat_1(sK255) ),
    inference(cnf_transformation,[],[f2884])).

fof(f4705,plain,(
    v5_ordinal1(sK255) ),
    inference(cnf_transformation,[],[f2884])).

fof(f4704,plain,(
    v1_funct_1(sK255) ),
    inference(cnf_transformation,[],[f2884])).

fof(f4703,plain,(
    v5_relat_1(sK255,sK253) ),
    inference(cnf_transformation,[],[f2884])).

fof(f4702,plain,(
    v1_relat_1(sK255) ),
    inference(cnf_transformation,[],[f2884])).

fof(f4701,plain,(
    r1_tarski(sK253,sK254) ),
    inference(cnf_transformation,[],[f2884])).

cnf(c_1253,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4152])).

cnf(c_79419,plain,
    ( ~ v5_relat_1(sK255,X0)
    | v5_relat_1(sK255,sK254)
    | ~ r1_tarski(X0,sK254)
    | ~ v1_relat_1(sK255) ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_81322,plain,
    ( ~ v5_relat_1(sK255,sK253)
    | v5_relat_1(sK255,sK254)
    | ~ r1_tarski(sK253,sK254)
    | ~ v1_relat_1(sK255) ),
    inference(instantiation,[status(thm)],[c_79419])).

cnf(c_1801,negated_conjecture,
    ( ~ v5_relat_1(sK255,sK254)
    | ~ v5_ordinal1(sK255)
    | ~ v1_funct_1(sK255)
    | ~ v1_relat_1(sK255) ),
    inference(cnf_transformation,[],[f4706])).

cnf(c_1802,negated_conjecture,
    ( v5_ordinal1(sK255) ),
    inference(cnf_transformation,[],[f4705])).

cnf(c_1803,negated_conjecture,
    ( v1_funct_1(sK255) ),
    inference(cnf_transformation,[],[f4704])).

cnf(c_1804,negated_conjecture,
    ( v5_relat_1(sK255,sK253) ),
    inference(cnf_transformation,[],[f4703])).

cnf(c_1805,negated_conjecture,
    ( v1_relat_1(sK255) ),
    inference(cnf_transformation,[],[f4702])).

cnf(c_1806,negated_conjecture,
    ( r1_tarski(sK253,sK254) ),
    inference(cnf_transformation,[],[f4701])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_81322,c_1801,c_1802,c_1803,c_1804,c_1805,c_1806])).

%------------------------------------------------------------------------------
