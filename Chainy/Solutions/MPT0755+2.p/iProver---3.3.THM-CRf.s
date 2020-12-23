%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0755+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 23.77s
% Output     : CNFRefutation 23.77s
% Verified   : 
% Statistics : Number of formulae       :   43 (  78 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  180 ( 545 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1070,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2142,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1070])).

fof(f2143,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2142])).

fof(f4637,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2143])).

fof(f669,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1583,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f669])).

fof(f3977,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1583])).

fof(f926,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1906,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f926])).

fof(f1907,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1906])).

fof(f4333,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1907])).

fof(f1073,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v5_ordinal1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2146,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1073])).

fof(f2147,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2146])).

fof(f4643,plain,(
    ! [X0,X1] :
      ( v5_ordinal1(k7_relat_1(X0,X1))
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2147])).

fof(f1109,conjecture,(
    ! [X0,X1] :
      ( ( v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( v5_ordinal1(k7_relat_1(X1,X2))
            & v1_funct_1(k7_relat_1(X1,X2))
            & v5_relat_1(k7_relat_1(X1,X2),X0)
            & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1110,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( v5_ordinal1(k7_relat_1(X1,X2))
              & v1_funct_1(k7_relat_1(X1,X2))
              & v5_relat_1(k7_relat_1(X1,X2),X0)
              & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1109])).

fof(f2188,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1110])).

fof(f2189,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f2188])).

fof(f2892,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
     => ( ( ~ v5_ordinal1(k7_relat_1(X1,sK255))
          | ~ v1_funct_1(k7_relat_1(X1,sK255))
          | ~ v5_relat_1(k7_relat_1(X1,sK255),X0)
          | ~ v1_relat_1(k7_relat_1(X1,sK255)) )
        & v3_ordinal1(sK255) ) ) ),
    introduced(choice_axiom,[])).

fof(f2891,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
              | ~ v1_funct_1(k7_relat_1(X1,X2))
              | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
              | ~ v1_relat_1(k7_relat_1(X1,X2)) )
            & v3_ordinal1(X2) )
        & v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(sK254,X2))
            | ~ v1_funct_1(k7_relat_1(sK254,X2))
            | ~ v5_relat_1(k7_relat_1(sK254,X2),sK253)
            | ~ v1_relat_1(k7_relat_1(sK254,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(sK254)
      & v1_funct_1(sK254)
      & v5_relat_1(sK254,sK253)
      & v1_relat_1(sK254) ) ),
    introduced(choice_axiom,[])).

fof(f2893,plain,
    ( ( ~ v5_ordinal1(k7_relat_1(sK254,sK255))
      | ~ v1_funct_1(k7_relat_1(sK254,sK255))
      | ~ v5_relat_1(k7_relat_1(sK254,sK255),sK253)
      | ~ v1_relat_1(k7_relat_1(sK254,sK255)) )
    & v3_ordinal1(sK255)
    & v5_ordinal1(sK254)
    & v1_funct_1(sK254)
    & v5_relat_1(sK254,sK253)
    & v1_relat_1(sK254) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK253,sK254,sK255])],[f2189,f2892,f2891])).

fof(f4724,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK254,sK255))
    | ~ v1_funct_1(k7_relat_1(sK254,sK255))
    | ~ v5_relat_1(k7_relat_1(sK254,sK255),sK253)
    | ~ v1_relat_1(k7_relat_1(sK254,sK255)) ),
    inference(cnf_transformation,[],[f2893])).

fof(f4723,plain,(
    v3_ordinal1(sK255) ),
    inference(cnf_transformation,[],[f2893])).

fof(f4722,plain,(
    v5_ordinal1(sK254) ),
    inference(cnf_transformation,[],[f2893])).

fof(f4721,plain,(
    v1_funct_1(sK254) ),
    inference(cnf_transformation,[],[f2893])).

fof(f4720,plain,(
    v5_relat_1(sK254,sK253) ),
    inference(cnf_transformation,[],[f2893])).

fof(f4719,plain,(
    v1_relat_1(sK254) ),
    inference(cnf_transformation,[],[f2893])).

cnf(c_1727,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(k7_relat_1(X0,X2),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4637])).

cnf(c_80136,plain,
    ( v5_relat_1(k7_relat_1(sK254,sK255),sK253)
    | ~ v5_relat_1(sK254,sK253)
    | ~ v1_relat_1(sK254) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_1069,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3977])).

cnf(c_79507,plain,
    ( v1_relat_1(k7_relat_1(sK254,sK255))
    | ~ v1_relat_1(sK254) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1424,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4333])).

cnf(c_79412,plain,
    ( v1_funct_1(k7_relat_1(sK254,sK255))
    | ~ v1_funct_1(sK254)
    | ~ v1_relat_1(sK254) ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_1732,plain,
    ( ~ v5_ordinal1(X0)
    | v5_ordinal1(k7_relat_1(X0,X1))
    | ~ v3_ordinal1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4643])).

cnf(c_79355,plain,
    ( v5_ordinal1(k7_relat_1(sK254,sK255))
    | ~ v5_ordinal1(sK254)
    | ~ v3_ordinal1(sK255)
    | ~ v1_funct_1(sK254)
    | ~ v1_relat_1(sK254) ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_1810,negated_conjecture,
    ( ~ v5_relat_1(k7_relat_1(sK254,sK255),sK253)
    | ~ v5_ordinal1(k7_relat_1(sK254,sK255))
    | ~ v1_funct_1(k7_relat_1(sK254,sK255))
    | ~ v1_relat_1(k7_relat_1(sK254,sK255)) ),
    inference(cnf_transformation,[],[f4724])).

cnf(c_1811,negated_conjecture,
    ( v3_ordinal1(sK255) ),
    inference(cnf_transformation,[],[f4723])).

cnf(c_1812,negated_conjecture,
    ( v5_ordinal1(sK254) ),
    inference(cnf_transformation,[],[f4722])).

cnf(c_1813,negated_conjecture,
    ( v1_funct_1(sK254) ),
    inference(cnf_transformation,[],[f4721])).

cnf(c_1814,negated_conjecture,
    ( v5_relat_1(sK254,sK253) ),
    inference(cnf_transformation,[],[f4720])).

cnf(c_1815,negated_conjecture,
    ( v1_relat_1(sK254) ),
    inference(cnf_transformation,[],[f4719])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_80136,c_79507,c_79412,c_79355,c_1810,c_1811,c_1812,c_1813,c_1814,c_1815])).

%------------------------------------------------------------------------------
