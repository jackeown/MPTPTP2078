%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:47 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 225 expanded)
%              Number of clauses        :   41 (  84 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  234 (1070 expanded)
%              Number of equality atoms :   41 ( 277 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(c_0_9,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X28 = k1_funct_1(X29,X27)
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X27,k1_relat_1(X29))
        | X28 != k1_funct_1(X29,X27)
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_11,plain,(
    ! [X19] :
      ( ( k2_relat_1(X19) = k1_relat_1(k4_relat_1(X19))
        | ~ v1_relat_1(X19) )
      & ( k1_relat_1(X19) = k2_relat_1(k4_relat_1(X19))
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X10,X9),X5)
        | r2_hidden(X9,X6)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v2_funct_1(esk5_0)
    & r2_hidden(esk4_0,k2_relat_1(esk5_0))
    & ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
      | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X21] :
      ( ( v1_relat_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(k4_relat_1(X2),X1)),k4_relat_1(X2))
    | ~ v1_funct_1(k4_relat_1(X2))
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X20] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v2_funct_1(X20)
      | k2_funct_1(X20) = k4_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(k4_relat_1(esk5_0),esk4_0)),k4_relat_1(esk5_0))
    | ~ v1_funct_1(k4_relat_1(esk5_0))
    | ~ v1_relat_1(k4_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_30,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])])).

cnf(c_0_32,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
    | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(k4_tarski(X4,X2),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_25])).

fof(c_0_35,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ r2_hidden(X22,k1_relat_1(X23))
      | k1_funct_1(k5_relat_1(X23,X24),X22) = k1_funct_1(X24,k1_funct_1(X23,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k4_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_24]),c_0_21])])).

cnf(c_0_39,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_41,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(k4_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24]),c_0_21])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(esk4_0,k1_relat_1(k2_funct_1(esk5_0)))
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24]),c_0_21]),c_0_31])]),c_0_34])).

cnf(c_0_45,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_30])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(k2_funct_1(X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_20]),c_0_32]),c_0_24]),c_0_21])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32]),c_0_24]),c_0_21])])).

fof(c_0_50,plain,(
    ! [X25,X26] :
      ( ( X25 = k1_funct_1(k2_funct_1(X26),k1_funct_1(X26,X25))
        | ~ v2_funct_1(X26)
        | ~ r2_hidden(X25,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X25 = k1_funct_1(k5_relat_1(X26,k2_funct_1(X26)),X25)
        | ~ v2_funct_1(X26)
        | ~ r2_hidden(X25,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

fof(c_0_51,plain,(
    ! [X16,X17,X18] :
      ( ( r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(X17,k2_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_24]),c_0_21])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_49]),c_0_24]),c_0_21])])).

cnf(c_0_54,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk5_0),esk4_0),esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24]),c_0_21])])).

cnf(c_0_57,plain,
    ( k1_funct_1(k2_funct_1(X1),X2) = X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_25]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_32]),c_0_24]),c_0_21])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_37]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:56:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.87/1.08  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.87/1.08  # and selection function PSelectUnlessUniqMaxPos.
% 0.87/1.08  #
% 0.87/1.08  # Preprocessing time       : 0.028 s
% 0.87/1.08  # Presaturation interreduction done
% 0.87/1.08  
% 0.87/1.08  # Proof found!
% 0.87/1.08  # SZS status Theorem
% 0.87/1.08  # SZS output start CNFRefutation
% 0.87/1.08  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.87/1.08  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.87/1.08  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 0.87/1.08  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.87/1.08  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.87/1.08  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 0.87/1.08  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 0.87/1.08  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 0.87/1.08  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.87/1.08  fof(c_0_9, plain, ![X27, X28, X29]:(((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X28=k1_funct_1(X29,X27)|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X27,k1_relat_1(X29))|X28!=k1_funct_1(X29,X27)|r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.87/1.08  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.87/1.08  fof(c_0_11, plain, ![X19]:((k2_relat_1(X19)=k1_relat_1(k4_relat_1(X19))|~v1_relat_1(X19))&(k1_relat_1(X19)=k2_relat_1(k4_relat_1(X19))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.87/1.08  fof(c_0_12, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 0.87/1.08  fof(c_0_13, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)|X6!=k2_relat_1(X5))&(~r2_hidden(k4_tarski(X10,X9),X5)|r2_hidden(X9,X6)|X6!=k2_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.87/1.08  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_10])).
% 0.87/1.08  cnf(c_0_15, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.87/1.08  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v2_funct_1(esk5_0)&r2_hidden(esk4_0,k2_relat_1(esk5_0)))&(esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.87/1.08  fof(c_0_17, plain, ![X21]:((v1_relat_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(v1_funct_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.87/1.08  cnf(c_0_18, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.08  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(k4_relat_1(X2),X1)),k4_relat_1(X2))|~v1_funct_1(k4_relat_1(X2))|~v1_relat_1(k4_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.87/1.08  cnf(c_0_20, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.87/1.08  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.87/1.08  fof(c_0_22, plain, ![X20]:(~v1_relat_1(X20)|~v1_funct_1(X20)|(~v2_funct_1(X20)|k2_funct_1(X20)=k4_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.87/1.08  cnf(c_0_23, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.87/1.08  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.87/1.08  cnf(c_0_25, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.87/1.08  cnf(c_0_26, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_18])).
% 0.87/1.08  cnf(c_0_27, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.87/1.08  cnf(c_0_28, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.08  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_funct_1(k4_relat_1(esk5_0),esk4_0)),k4_relat_1(esk5_0))|~v1_funct_1(k4_relat_1(esk5_0))|~v1_relat_1(k4_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.87/1.08  cnf(c_0_30, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.87/1.08  cnf(c_0_31, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_32, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.87/1.08  cnf(c_0_33, negated_conjecture, (esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.87/1.08  cnf(c_0_34, plain, (X1=X2|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(k4_tarski(X4,X2),X3)), inference(spm,[status(thm)],[c_0_25, c_0_25])).
% 0.87/1.08  fof(c_0_35, plain, ![X22, X23, X24]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v1_relat_1(X24)|~v1_funct_1(X24)|(~r2_hidden(X22,k1_relat_1(X23))|k1_funct_1(k5_relat_1(X23,X24),X22)=k1_funct_1(X24,k1_funct_1(X23,X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.87/1.08  cnf(c_0_36, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X1),k4_relat_1(X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.87/1.08  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_28])).
% 0.87/1.08  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_39, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.87/1.08  cnf(c_0_40, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)!=esk4_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34])])).
% 0.87/1.08  cnf(c_0_41, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.87/1.08  cnf(c_0_42, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(k4_relat_1(X2)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.87/1.08  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_44, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(esk4_0,k1_relat_1(k2_funct_1(esk5_0)))|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24]), c_0_21]), c_0_31])]), c_0_34])).
% 0.87/1.08  cnf(c_0_45, plain, (k1_relat_1(k2_funct_1(X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_30])).
% 0.87/1.08  cnf(c_0_46, plain, (r2_hidden(X1,k1_relat_1(X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(k2_funct_1(X2)))), inference(spm,[status(thm)],[c_0_42, c_0_30])).
% 0.87/1.08  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k2_relat_1(k2_funct_1(esk5_0)))), inference(spm,[status(thm)],[c_0_26, c_0_43])).
% 0.87/1.08  cnf(c_0_48, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_20]), c_0_32]), c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_49, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32]), c_0_24]), c_0_21])])).
% 0.87/1.08  fof(c_0_50, plain, ![X25, X26]:((X25=k1_funct_1(k2_funct_1(X26),k1_funct_1(X26,X25))|(~v2_funct_1(X26)|~r2_hidden(X25,k1_relat_1(X26)))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(X25=k1_funct_1(k5_relat_1(X26,k2_funct_1(X26)),X25)|(~v2_funct_1(X26)|~r2_hidden(X25,k1_relat_1(X26)))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.87/1.08  fof(c_0_51, plain, ![X16, X17, X18]:((r2_hidden(X16,k1_relat_1(X18))|~r2_hidden(k4_tarski(X16,X17),X18)|~v1_relat_1(X18))&(r2_hidden(X17,k2_relat_1(X18))|~r2_hidden(k4_tarski(X16,X17),X18)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.87/1.08  cnf(c_0_52, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_39]), c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_49]), c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_54, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.87/1.08  cnf(c_0_55, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.87/1.08  cnf(c_0_56, negated_conjecture, (~r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk5_0),esk4_0),esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_57, plain, (k1_funct_1(k2_funct_1(X1),X2)=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_25]), c_0_55])).
% 0.87/1.08  cnf(c_0_58, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_32]), c_0_24]), c_0_21])])).
% 0.87/1.08  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_37]), c_0_20])]), ['proof']).
% 0.87/1.08  # SZS output end CNFRefutation
% 0.87/1.08  # Proof object total steps             : 60
% 0.87/1.08  # Proof object clause steps            : 41
% 0.87/1.08  # Proof object formula steps           : 19
% 0.87/1.08  # Proof object conjectures             : 22
% 0.87/1.08  # Proof object clause conjectures      : 19
% 0.87/1.08  # Proof object formula conjectures     : 3
% 0.87/1.08  # Proof object initial clauses used    : 17
% 0.87/1.08  # Proof object initial formulas used   : 9
% 0.87/1.08  # Proof object generating inferences   : 21
% 0.87/1.08  # Proof object simplifying inferences  : 46
% 0.87/1.08  # Training examples: 0 positive, 0 negative
% 0.87/1.08  # Parsed axioms                        : 9
% 0.87/1.08  # Removed by relevancy pruning/SinE    : 0
% 0.87/1.08  # Initial clauses                      : 22
% 0.87/1.08  # Removed in clause preprocessing      : 0
% 0.87/1.08  # Initial clauses in saturation        : 22
% 0.87/1.08  # Processed clauses                    : 998
% 0.87/1.08  # ...of these trivial                  : 3
% 0.87/1.08  # ...subsumed                          : 259
% 0.87/1.08  # ...remaining for further processing  : 736
% 0.87/1.08  # Other redundant clauses eliminated   : 1158
% 0.87/1.08  # Clauses deleted for lack of memory   : 0
% 0.87/1.08  # Backward-subsumed                    : 128
% 0.87/1.08  # Backward-rewritten                   : 30
% 0.87/1.08  # Generated clauses                    : 54755
% 0.87/1.08  # ...of the previous two non-trivial   : 53532
% 0.87/1.08  # Contextual simplify-reflections      : 34
% 0.87/1.08  # Paramodulations                      : 53595
% 0.87/1.08  # Factorizations                       : 2
% 0.87/1.08  # Equation resolutions                 : 1158
% 0.87/1.08  # Propositional unsat checks           : 0
% 0.87/1.08  #    Propositional check models        : 0
% 0.87/1.08  #    Propositional check unsatisfiable : 0
% 0.87/1.08  #    Propositional clauses             : 0
% 0.87/1.08  #    Propositional clauses after purity: 0
% 0.87/1.08  #    Propositional unsat core size     : 0
% 0.87/1.08  #    Propositional preprocessing time  : 0.000
% 0.87/1.08  #    Propositional encoding time       : 0.000
% 0.87/1.08  #    Propositional solver time         : 0.000
% 0.87/1.08  #    Success case prop preproc time    : 0.000
% 0.87/1.08  #    Success case prop encoding time   : 0.000
% 0.87/1.08  #    Success case prop solver time     : 0.000
% 0.87/1.08  # Current number of processed clauses  : 555
% 0.87/1.08  #    Positive orientable unit clauses  : 58
% 0.87/1.08  #    Positive unorientable unit clauses: 0
% 0.87/1.08  #    Negative unit clauses             : 4
% 0.87/1.08  #    Non-unit-clauses                  : 493
% 0.87/1.08  # Current number of unprocessed clauses: 52532
% 0.87/1.08  # ...number of literals in the above   : 406136
% 0.87/1.08  # Current number of archived formulas  : 0
% 0.87/1.08  # Current number of archived clauses   : 178
% 0.87/1.08  # Clause-clause subsumption calls (NU) : 25965
% 0.87/1.08  # Rec. Clause-clause subsumption calls : 4846
% 0.87/1.08  # Non-unit clause-clause subsumptions  : 359
% 0.87/1.08  # Unit Clause-clause subsumption calls : 472
% 0.87/1.08  # Rewrite failures with RHS unbound    : 0
% 0.87/1.08  # BW rewrite match attempts            : 718
% 0.87/1.08  # BW rewrite match successes           : 4
% 0.87/1.08  # Condensation attempts                : 0
% 0.87/1.08  # Condensation successes               : 0
% 0.87/1.08  # Termbank termtop insertions          : 1606916
% 0.87/1.09  
% 0.87/1.09  # -------------------------------------------------
% 0.87/1.09  # User time                : 0.711 s
% 0.87/1.09  # System time              : 0.028 s
% 0.87/1.09  # Total time               : 0.739 s
% 0.87/1.09  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
