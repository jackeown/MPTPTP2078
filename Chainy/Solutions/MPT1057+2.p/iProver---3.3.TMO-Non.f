%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1057+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Timeout 59.56s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   24 (  38 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 129 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f766,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2247,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f766])).

fof(f6036,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2247])).

fof(f1583,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X2,X1)
         => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1584,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1583])).

fof(f3325,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1584])).

fof(f3326,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f3325])).

fof(f4788,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
     => ( k9_relat_1(X0,sK564) != k9_relat_1(k7_relat_1(X0,sK563),sK564)
        & r1_tarski(sK564,sK563) ) ) ),
    introduced(choice_axiom,[])).

fof(f4787,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(X2,X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK562,X2) != k9_relat_1(k7_relat_1(sK562,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(sK562)
      & v1_relat_1(sK562) ) ),
    introduced(choice_axiom,[])).

fof(f4789,plain,
    ( k9_relat_1(sK562,sK564) != k9_relat_1(k7_relat_1(sK562,sK563),sK564)
    & r1_tarski(sK564,sK563)
    & v1_funct_1(sK562)
    & v1_relat_1(sK562) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK562,sK563,sK564])],[f3326,f4788,f4787])).

fof(f7848,plain,(
    k9_relat_1(sK562,sK564) != k9_relat_1(k7_relat_1(sK562,sK563),sK564) ),
    inference(cnf_transformation,[],[f4789])).

fof(f7847,plain,(
    r1_tarski(sK564,sK563) ),
    inference(cnf_transformation,[],[f4789])).

fof(f7845,plain,(
    v1_relat_1(sK562) ),
    inference(cnf_transformation,[],[f4789])).

cnf(c_1187,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f6036])).

cnf(c_216925,plain,
    ( ~ r1_tarski(sK564,sK563)
    | ~ v1_relat_1(sK562)
    | k9_relat_1(k7_relat_1(sK562,sK563),sK564) = k9_relat_1(sK562,sK564) ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_44924,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_153181,plain,
    ( k9_relat_1(sK562,sK564) = k9_relat_1(sK562,sK564) ),
    inference(instantiation,[status(thm)],[c_44924])).

cnf(c_44925,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_127454,plain,
    ( k9_relat_1(k7_relat_1(sK562,sK563),sK564) != X0
    | k9_relat_1(sK562,sK564) != X0
    | k9_relat_1(sK562,sK564) = k9_relat_1(k7_relat_1(sK562,sK563),sK564) ),
    inference(instantiation,[status(thm)],[c_44925])).

cnf(c_153180,plain,
    ( k9_relat_1(k7_relat_1(sK562,sK563),sK564) != k9_relat_1(sK562,sK564)
    | k9_relat_1(sK562,sK564) = k9_relat_1(k7_relat_1(sK562,sK563),sK564)
    | k9_relat_1(sK562,sK564) != k9_relat_1(sK562,sK564) ),
    inference(instantiation,[status(thm)],[c_127454])).

cnf(c_2984,negated_conjecture,
    ( k9_relat_1(sK562,sK564) != k9_relat_1(k7_relat_1(sK562,sK563),sK564) ),
    inference(cnf_transformation,[],[f7848])).

cnf(c_2985,negated_conjecture,
    ( r1_tarski(sK564,sK563) ),
    inference(cnf_transformation,[],[f7847])).

cnf(c_2987,negated_conjecture,
    ( v1_relat_1(sK562) ),
    inference(cnf_transformation,[],[f7845])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_216925,c_153181,c_153180,c_2984,c_2985,c_2987])).

%------------------------------------------------------------------------------
