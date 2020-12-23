%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0708+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 31.37s
% Output     : CNFRefutation 31.37s
% Verified   : 
% Statistics : Number of formulae       :   34 (  52 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  101 ( 206 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f780,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1614,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f780])).

fof(f1615,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1614])).

fof(f3822,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1615])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1079,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f1080,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1079])).

fof(f2724,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1080])).

fof(f947,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1843,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f947])).

fof(f1844,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1843])).

fof(f4099,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1844])).

fof(f966,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f967,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f966])).

fof(f1878,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f967])).

fof(f1879,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1878])).

fof(f2546,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
        & r1_tarski(k9_relat_1(X2,X0),X1)
        & r1_tarski(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK208,k10_relat_1(sK210,sK209))
      & r1_tarski(k9_relat_1(sK210,sK208),sK209)
      & r1_tarski(sK208,k1_relat_1(sK210))
      & v1_funct_1(sK210)
      & v1_relat_1(sK210) ) ),
    introduced(choice_axiom,[])).

fof(f2547,plain,
    ( ~ r1_tarski(sK208,k10_relat_1(sK210,sK209))
    & r1_tarski(k9_relat_1(sK210,sK208),sK209)
    & r1_tarski(sK208,k1_relat_1(sK210))
    & v1_funct_1(sK210)
    & v1_relat_1(sK210) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK208,sK209,sK210])],[f1879,f2546])).

fof(f4126,plain,(
    ~ r1_tarski(sK208,k10_relat_1(sK210,sK209)) ),
    inference(cnf_transformation,[],[f2547])).

fof(f4125,plain,(
    r1_tarski(k9_relat_1(sK210,sK208),sK209) ),
    inference(cnf_transformation,[],[f2547])).

fof(f4124,plain,(
    r1_tarski(sK208,k1_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f2547])).

fof(f4122,plain,(
    v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f2547])).

cnf(c_1203,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f3822])).

cnf(c_116238,plain,
    ( r1_tarski(k10_relat_1(sK210,k9_relat_1(sK210,sK208)),k10_relat_1(sK210,sK209))
    | ~ r1_tarski(k9_relat_1(sK210,sK208),sK209)
    | ~ v1_relat_1(sK210) ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f2724])).

cnf(c_74616,plain,
    ( ~ r1_tarski(X0,k10_relat_1(sK210,sK209))
    | ~ r1_tarski(sK208,X0)
    | r1_tarski(sK208,k10_relat_1(sK210,sK209)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_89470,plain,
    ( ~ r1_tarski(k10_relat_1(sK210,k9_relat_1(sK210,sK208)),k10_relat_1(sK210,sK209))
    | ~ r1_tarski(sK208,k10_relat_1(sK210,k9_relat_1(sK210,sK208)))
    | r1_tarski(sK208,k10_relat_1(sK210,sK209)) ),
    inference(instantiation,[status(thm)],[c_74616])).

cnf(c_1480,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4099])).

cnf(c_76474,plain,
    ( r1_tarski(sK208,k10_relat_1(sK210,k9_relat_1(sK210,sK208)))
    | ~ r1_tarski(sK208,k1_relat_1(sK210))
    | ~ v1_relat_1(sK210) ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_1503,negated_conjecture,
    ( ~ r1_tarski(sK208,k10_relat_1(sK210,sK209)) ),
    inference(cnf_transformation,[],[f4126])).

cnf(c_1504,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK210,sK208),sK209) ),
    inference(cnf_transformation,[],[f4125])).

cnf(c_1505,negated_conjecture,
    ( r1_tarski(sK208,k1_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f4124])).

cnf(c_1507,negated_conjecture,
    ( v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f4122])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_116238,c_89470,c_76474,c_1503,c_1504,c_1505,c_1507])).

%------------------------------------------------------------------------------
