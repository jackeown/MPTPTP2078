%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0670+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:50 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   33 (  58 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  121 ( 209 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
       => k1_funct_1(k8_relat_1(X2,X3),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t117_relat_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',dt_k8_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
         => k1_funct_1(k8_relat_1(X2,X3),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t87_funct_1])).

fof(c_0_8,plain,(
    ! [X2325,X2326] :
      ( ~ v1_relat_1(X2326)
      | r1_tarski(k8_relat_1(X2325,X2326),X2326) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk200_0)
    & v1_funct_1(esk200_0)
    & r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0)))
    & k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0) != k1_funct_1(esk200_0,esk198_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X2719,X2720,X2721] :
      ( ( X2721 != k1_funct_1(X2719,X2720)
        | r2_hidden(k4_tarski(X2720,X2721),X2719)
        | ~ r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) )
      & ( ~ r2_hidden(k4_tarski(X2720,X2721),X2719)
        | X2721 = k1_funct_1(X2719,X2720)
        | ~ r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) )
      & ( X2721 != k1_funct_1(X2719,X2720)
        | X2721 = k1_xboole_0
        | r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) )
      & ( X2721 != k1_xboole_0
        | X2721 = k1_funct_1(X2719,X2720)
        | r2_hidden(X2720,k1_relat_1(X2719))
        | ~ v1_relat_1(X2719)
        | ~ v1_funct_1(X2719) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_11,plain,(
    ! [X2759,X2760] :
      ( ( v1_relat_1(k8_relat_1(X2759,X2760))
        | ~ v1_relat_1(X2760)
        | ~ v1_funct_1(X2760) )
      & ( v1_funct_1(k8_relat_1(X2759,X2760))
        | ~ v1_relat_1(X2760)
        | ~ v1_funct_1(X2760) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

fof(c_0_12,plain,(
    ! [X2229,X2230] :
      ( ~ v1_relat_1(X2230)
      | v1_relat_1(k8_relat_1(X2229,X2230)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_13,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk200_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk200_0),esk200_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk198_0,k1_relat_1(k8_relat_1(esk199_0,esk200_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(k8_relat_1(X1,esk200_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk200_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

fof(c_0_26,plain,(
    ! [X2945,X2946,X2947] :
      ( ( r2_hidden(X2945,k1_relat_1(X2947))
        | ~ r2_hidden(k4_tarski(X2945,X2946),X2947)
        | ~ v1_relat_1(X2947)
        | ~ v1_funct_1(X2947) )
      & ( X2946 = k1_funct_1(X2947,X2945)
        | ~ r2_hidden(k4_tarski(X2945,X2946),X2947)
        | ~ v1_relat_1(X2947)
        | ~ v1_funct_1(X2947) )
      & ( ~ r2_hidden(X2945,k1_relat_1(X2947))
        | X2946 != k1_funct_1(X2947,X2945)
        | r2_hidden(k4_tarski(X2945,X2946),X2947)
        | ~ v1_relat_1(X2947)
        | ~ v1_funct_1(X2947) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk200_0)
    | ~ r2_hidden(X1,k8_relat_1(X2,esk200_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk198_0,k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0)),k8_relat_1(esk199_0,esk200_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_29,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk198_0,k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0)),esk200_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk199_0,esk200_0),esk198_0) != k1_funct_1(esk200_0,esk198_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_18]),c_0_15])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
