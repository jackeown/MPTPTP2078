%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0614+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 34.99s
% Output     : CNFRefutation 34.99s
% Verified   : 
% Statistics : Number of formulae       :   32 (  56 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 206 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1344,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f2023,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1344])).

fof(f3150,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2023])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f944,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f945,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f944])).

fof(f2221,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f945])).

fof(f3151,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2023])).

fof(f823,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f824,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v5_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f823])).

fof(f1543,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f824])).

fof(f1544,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1543])).

fof(f2088,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ~ v5_relat_1(sK166,X1)
        & v5_relat_1(sK166,X0)
        & v1_relat_1(sK166) ) ) ),
    introduced(choice_axiom,[])).

fof(f2087,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v5_relat_1(X2,X1)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v5_relat_1(X2,sK165)
          & v5_relat_1(X2,sK164)
          & v1_relat_1(X2) )
      & r1_tarski(sK164,sK165) ) ),
    introduced(choice_axiom,[])).

fof(f2089,plain,
    ( ~ v5_relat_1(sK166,sK165)
    & v5_relat_1(sK166,sK164)
    & v1_relat_1(sK166)
    & r1_tarski(sK164,sK165) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK164,sK165,sK166])],[f1544,f2088,f2087])).

fof(f3370,plain,(
    ~ v5_relat_1(sK166,sK165) ),
    inference(cnf_transformation,[],[f2089])).

fof(f3369,plain,(
    v5_relat_1(sK166,sK164) ),
    inference(cnf_transformation,[],[f2089])).

fof(f3368,plain,(
    v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f2089])).

fof(f3367,plain,(
    r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f2089])).

cnf(c_1035,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3150])).

cnf(c_132128,plain,
    ( ~ v5_relat_1(sK166,sK164)
    | r1_tarski(k2_relat_1(sK166),sK164)
    | ~ v1_relat_1(sK166) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f2221])).

cnf(c_74806,plain,
    ( ~ r1_tarski(X0,sK165)
    | ~ r1_tarski(k2_relat_1(sK166),X0)
    | r1_tarski(k2_relat_1(sK166),sK165) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_98860,plain,
    ( ~ r1_tarski(k2_relat_1(sK166),sK164)
    | r1_tarski(k2_relat_1(sK166),sK165)
    | ~ r1_tarski(sK164,sK165) ),
    inference(instantiation,[status(thm)],[c_74806])).

cnf(c_1034,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3151])).

cnf(c_64154,plain,
    ( v5_relat_1(sK166,sK165)
    | ~ r1_tarski(k2_relat_1(sK166),sK165)
    | ~ v1_relat_1(sK166) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_1251,negated_conjecture,
    ( ~ v5_relat_1(sK166,sK165) ),
    inference(cnf_transformation,[],[f3370])).

cnf(c_1252,negated_conjecture,
    ( v5_relat_1(sK166,sK164) ),
    inference(cnf_transformation,[],[f3369])).

cnf(c_1253,negated_conjecture,
    ( v1_relat_1(sK166) ),
    inference(cnf_transformation,[],[f3368])).

cnf(c_1254,negated_conjecture,
    ( r1_tarski(sK164,sK165) ),
    inference(cnf_transformation,[],[f3367])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_132128,c_98860,c_64154,c_1251,c_1252,c_1253,c_1254])).

%------------------------------------------------------------------------------
