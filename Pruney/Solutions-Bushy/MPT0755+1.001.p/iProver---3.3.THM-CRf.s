%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0755+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:03 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   47 (  82 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  191 ( 556 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v5_ordinal1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v5_ordinal1(k7_relat_1(X0,X1))
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
     => ( ( ~ v5_ordinal1(k7_relat_1(X1,sK2))
          | ~ v1_funct_1(k7_relat_1(X1,sK2))
          | ~ v5_relat_1(k7_relat_1(X1,sK2),X0)
          | ~ v1_relat_1(k7_relat_1(X1,sK2)) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
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
          ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
            | ~ v1_funct_1(k7_relat_1(sK1,X2))
            | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
            | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(sK1)
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
      | ~ v1_funct_1(k7_relat_1(sK1,sK2))
      | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
      | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
    & v3_ordinal1(sK2)
    & v5_ordinal1(sK1)
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17,f16])).

fof(f31,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    v5_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_264,plain,
    ( ~ v1_funct_1(X0_38)
    | v1_funct_1(k7_relat_1(X0_38,X0_40))
    | ~ v1_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_278,plain,
    ( v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_1,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(k7_relat_1(X0,X2),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_266,plain,
    ( ~ v5_relat_1(X0_38,X0_39)
    | v5_relat_1(k7_relat_1(X0_38,X0_40),X0_39)
    | ~ v1_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_272,plain,
    ( v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_267,plain,
    ( ~ v1_relat_1(X0_38)
    | v1_relat_1(k7_relat_1(X0_38,X0_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_269,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v5_ordinal1(X0)
    | v5_ordinal1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_9,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_159,plain,
    ( ~ v1_funct_1(X0)
    | ~ v5_ordinal1(X0)
    | v5_ordinal1(k7_relat_1(X0,sK2))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_3,c_9])).

cnf(c_161,plain,
    ( ~ v1_funct_1(sK1)
    | v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v5_ordinal1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_8,negated_conjecture,
    ( ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( v5_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_278,c_272,c_269,c_161,c_8,c_10,c_11,c_12,c_13])).


%------------------------------------------------------------------------------
