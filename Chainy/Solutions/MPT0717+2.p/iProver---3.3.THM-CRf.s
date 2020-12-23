%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0717+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 31.57s
% Output     : CNFRefutation 31.57s
% Verified   : 
% Statistics : Number of formulae       :   31 (  59 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 258 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f950,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1865,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f950])).

fof(f1866,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1865])).

fof(f4182,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1866])).

fof(f806,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1674,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f806])).

fof(f1675,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1674])).

fof(f3922,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1675])).

fof(f988,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f989,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f988])).

fof(f1936,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f989])).

fof(f1937,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1936])).

fof(f2620,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK217),X0)
        & r2_hidden(sK217,k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2619,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
            & r2_hidden(X2,k1_relat_1(X1)) )
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(sK216,X2),sK215)
          & r2_hidden(X2,k1_relat_1(sK216)) )
      & v1_funct_1(sK216)
      & v5_relat_1(sK216,sK215)
      & v1_relat_1(sK216) ) ),
    introduced(choice_axiom,[])).

fof(f2621,plain,
    ( ~ r2_hidden(k1_funct_1(sK216,sK217),sK215)
    & r2_hidden(sK217,k1_relat_1(sK216))
    & v1_funct_1(sK216)
    & v5_relat_1(sK216,sK215)
    & v1_relat_1(sK216) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK215,sK216,sK217])],[f1937,f2620,f2619])).

fof(f4243,plain,(
    ~ r2_hidden(k1_funct_1(sK216,sK217),sK215) ),
    inference(cnf_transformation,[],[f2621])).

fof(f4242,plain,(
    r2_hidden(sK217,k1_relat_1(sK216)) ),
    inference(cnf_transformation,[],[f2621])).

fof(f4241,plain,(
    v1_funct_1(sK216) ),
    inference(cnf_transformation,[],[f2621])).

fof(f4240,plain,(
    v5_relat_1(sK216,sK215) ),
    inference(cnf_transformation,[],[f2621])).

fof(f4239,plain,(
    v1_relat_1(sK216) ),
    inference(cnf_transformation,[],[f2621])).

cnf(c_1492,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4182])).

cnf(c_96285,plain,
    ( r2_hidden(k1_funct_1(sK216,sK217),k2_relat_1(sK216))
    | ~ r2_hidden(sK217,k1_relat_1(sK216))
    | ~ v1_funct_1(sK216)
    | ~ v1_relat_1(sK216) ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_1232,plain,
    ( ~ v5_relat_1(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3922])).

cnf(c_72527,plain,
    ( ~ v5_relat_1(X0,sK215)
    | ~ r2_hidden(k1_funct_1(sK216,sK217),k2_relat_1(X0))
    | r2_hidden(k1_funct_1(sK216,sK217),sK215)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_88070,plain,
    ( ~ v5_relat_1(sK216,sK215)
    | ~ r2_hidden(k1_funct_1(sK216,sK217),k2_relat_1(sK216))
    | r2_hidden(k1_funct_1(sK216,sK217),sK215)
    | ~ v1_relat_1(sK216) ),
    inference(instantiation,[status(thm)],[c_72527])).

cnf(c_1549,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK216,sK217),sK215) ),
    inference(cnf_transformation,[],[f4243])).

cnf(c_1550,negated_conjecture,
    ( r2_hidden(sK217,k1_relat_1(sK216)) ),
    inference(cnf_transformation,[],[f4242])).

cnf(c_1551,negated_conjecture,
    ( v1_funct_1(sK216) ),
    inference(cnf_transformation,[],[f4241])).

cnf(c_1552,negated_conjecture,
    ( v5_relat_1(sK216,sK215) ),
    inference(cnf_transformation,[],[f4240])).

cnf(c_1553,negated_conjecture,
    ( v1_relat_1(sK216) ),
    inference(cnf_transformation,[],[f4239])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96285,c_88070,c_1549,c_1550,c_1551,c_1552,c_1553])).

%------------------------------------------------------------------------------
