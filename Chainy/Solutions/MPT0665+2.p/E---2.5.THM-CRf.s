%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0665+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   35 (  92 expanded)
%              Number of clauses        :   20 (  34 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 331 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X1,X2) )
       => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t86_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t148_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k7_relat_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(X1,X2) )
         => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t73_funct_1])).

fof(c_0_8,plain,(
    ! [X2687,X2688,X2689] :
      ( ( r2_hidden(X2687,X2688)
        | ~ r2_hidden(X2687,k1_relat_1(k7_relat_1(X2689,X2688)))
        | ~ v1_relat_1(X2689) )
      & ( r2_hidden(X2687,k1_relat_1(X2689))
        | ~ r2_hidden(X2687,k1_relat_1(k7_relat_1(X2689,X2688)))
        | ~ v1_relat_1(X2689) )
      & ( ~ r2_hidden(X2687,X2688)
        | ~ r2_hidden(X2687,k1_relat_1(X2689))
        | r2_hidden(X2687,k1_relat_1(k7_relat_1(X2689,X2688)))
        | ~ v1_relat_1(X2689) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk198_0)
    & v1_funct_1(esk198_0)
    & r2_hidden(esk196_0,k1_relat_1(esk198_0))
    & r2_hidden(esk196_0,esk197_0)
    & ~ r2_hidden(k1_funct_1(esk198_0,esk196_0),k2_relat_1(k7_relat_1(esk198_0,esk197_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk196_0,esk197_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X2398,X2399] :
      ( ~ v1_relat_1(X2399)
      | k2_relat_1(k7_relat_1(X2399,X2398)) = k9_relat_1(X2399,X2398) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_13,plain,(
    ! [X2757,X2758] :
      ( ( v1_relat_1(k7_relat_1(X2757,X2758))
        | ~ v1_relat_1(X2757)
        | ~ v1_funct_1(X2757) )
      & ( v1_funct_1(k7_relat_1(X2757,X2758))
        | ~ v1_relat_1(X2757)
        | ~ v1_funct_1(X2757) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_14,plain,(
    ! [X2227,X2228] :
      ( ~ v1_relat_1(X2227)
      | v1_relat_1(k7_relat_1(X2227,X2228)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_15,plain,(
    ! [X2797,X2798] :
      ( ~ v1_relat_1(X2798)
      | ~ v1_funct_1(X2798)
      | ~ r2_hidden(X2797,k1_relat_1(X2798))
      | r2_hidden(k1_funct_1(X2798,X2797),k2_relat_1(X2798)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk196_0,k1_relat_1(k7_relat_1(X1,esk197_0)))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk196_0,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk196_0,k1_relat_1(esk198_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X2912,X2913,X2914] :
      ( ~ v1_relat_1(X2914)
      | ~ v1_funct_1(X2914)
      | ~ r2_hidden(X2912,k1_relat_1(k7_relat_1(X2914,X2913)))
      | k1_funct_1(k7_relat_1(X2914,X2913),X2912) = k1_funct_1(X2914,X2912) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_24,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk196_0,k1_relat_1(k7_relat_1(esk198_0,esk197_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk198_0,X1)) = k9_relat_1(esk198_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk198_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_18])])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk198_0,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_29,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk198_0,esk196_0),k2_relat_1(k7_relat_1(esk198_0,esk197_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_funct_1(k7_relat_1(esk198_0,esk197_0),esk196_0),k9_relat_1(esk198_0,esk197_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk198_0,esk197_0),esk196_0) = k1_funct_1(esk198_0,esk196_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_21]),c_0_18])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk198_0,esk196_0),k9_relat_1(esk198_0,esk197_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
