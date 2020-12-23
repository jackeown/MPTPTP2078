%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t25_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 181 expanded)
%              Number of clauses        :   26 (  61 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 959 expanded)
%              Number of equality atoms :   25 (  62 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t25_funct_1.p',d5_funct_1)).

fof(t25_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))
           => r2_hidden(X1,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t25_funct_1.p',t25_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t25_funct_1.p',fc2_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t25_funct_1.p',dt_k5_relat_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t25_funct_1.p',t22_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t25_funct_1.p',t21_funct_1)).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X14,X15,X16,X18] :
      ( ( r2_hidden(esk4_3(X10,X11,X12),k1_relat_1(X10))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X12 = k1_funct_1(X10,esk4_3(X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X15,k1_relat_1(X10))
        | X14 != k1_funct_1(X10,X15)
        | r2_hidden(X14,X11)
        | X11 != k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk5_2(X10,X16),X16)
        | ~ r2_hidden(X18,k1_relat_1(X10))
        | esk5_2(X10,X16) != k1_funct_1(X10,X18)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk6_2(X10,X16),k1_relat_1(X10))
        | r2_hidden(esk5_2(X10,X16),X16)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk5_2(X10,X16) = k1_funct_1(X10,esk6_2(X10,X16))
        | r2_hidden(esk5_2(X10,X16),X16)
        | X16 = k2_relat_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))
             => r2_hidden(X1,k2_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_funct_1])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk1_0,k2_relat_1(k5_relat_1(esk3_0,esk2_0)))
    & ~ r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,k2_relat_1(k5_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X39,X40] :
      ( ( v1_relat_1(k5_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( v1_funct_1(k5_relat_1(X39,X40))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0),k1_relat_1(k5_relat_1(esk3_0,esk2_0)))
    | ~ v1_funct_1(k5_relat_1(esk3_0,esk2_0))
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | v1_relat_1(k5_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_20,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ r2_hidden(X29,k1_relat_1(k5_relat_1(X31,X30)))
      | k1_funct_1(k5_relat_1(X31,X30),X29) = k1_funct_1(X30,k1_funct_1(X31,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0),k1_relat_1(k5_relat_1(esk3_0,esk2_0)))
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_22,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0),k1_relat_1(k5_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17]),c_0_18])])).

fof(c_0_26,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(X26,k1_relat_1(X28))
        | ~ r2_hidden(X26,k1_relat_1(k5_relat_1(X28,X27)))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(k1_funct_1(X28,X26),k1_relat_1(X27))
        | ~ r2_hidden(X26,k1_relat_1(k5_relat_1(X28,X27)))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(X26,k1_relat_1(X28))
        | ~ r2_hidden(k1_funct_1(X28,X26),k1_relat_1(X27))
        | r2_hidden(X26,k1_relat_1(k5_relat_1(X28,X27)))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_27,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk3_0,esk2_0),esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0)) = k1_funct_1(esk2_0,k1_funct_1(esk3_0,esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16]),c_0_15]),c_0_18]),c_0_17])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk2_0,k1_funct_1(esk3_0,esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0))) = esk1_0
    | ~ v1_funct_1(k5_relat_1(esk3_0,esk2_0))
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_11]),c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0)),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk2_0,k1_funct_1(esk3_0,esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0))) = esk1_0
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,k1_funct_1(esk3_0,esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0))),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15]),c_0_17])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk2_0,k1_funct_1(esk3_0,esk4_3(k5_relat_1(esk3_0,esk2_0),k2_relat_1(k5_relat_1(esk3_0,esk2_0)),esk1_0))) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_22]),c_0_17]),c_0_18])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
