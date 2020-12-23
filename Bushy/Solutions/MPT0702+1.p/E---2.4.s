%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t157_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:17 EDT 2019

% Result     : Theorem 234.92s
% Output     : CNFRefutation 234.92s
% Verified   : 
% Statistics : Number of formulae       :   37 (  97 expanded)
%              Number of clauses        :   28 (  37 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  194 ( 622 expanded)
%              Number of equality atoms :   33 (  75 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t157_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t157_funct_1.p',t157_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t157_funct_1.p',d8_funct_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t157_funct_1.p',d12_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t157_funct_1.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
            & r1_tarski(X1,k1_relat_1(X3))
            & v2_funct_1(X3) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t157_funct_1])).

fof(c_0_5,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v2_funct_1(X29)
        | ~ r2_hidden(X30,k1_relat_1(X29))
        | ~ r2_hidden(X31,k1_relat_1(X29))
        | k1_funct_1(X29,X30) != k1_funct_1(X29,X31)
        | X30 = X31
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk8_1(X29),k1_relat_1(X29))
        | v2_funct_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk9_1(X29),k1_relat_1(X29))
        | v2_funct_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_funct_1(X29,esk8_1(X29)) = k1_funct_1(X29,esk9_1(X29))
        | v2_funct_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( esk8_1(X29) != esk9_1(X29)
        | v2_funct_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k1_relat_1(esk3_0))
    & v2_funct_1(esk3_0)
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(esk4_4(X11,X12,X13,X14),k1_relat_1(X11))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk4_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X14 = k1_funct_1(X11,esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X17,k1_relat_1(X11))
        | ~ r2_hidden(X17,X12)
        | X16 != k1_funct_1(X11,X17)
        | r2_hidden(X16,X13)
        | X13 != k9_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk5_3(X11,X18,X19),X19)
        | ~ r2_hidden(X21,k1_relat_1(X11))
        | ~ r2_hidden(X21,X18)
        | esk5_3(X11,X18,X19) != k1_funct_1(X11,X21)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_3(X11,X18,X19),k1_relat_1(X11))
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_3(X11,X18,X19),X18)
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk5_3(X11,X18,X19) = k1_funct_1(X11,esk6_3(X11,X18,X19))
        | r2_hidden(esk5_3(X11,X18,X19),X19)
        | X19 = k9_relat_1(X11,X18)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_8,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( X1 = k1_funct_1(X2,esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk3_0,X1) != k1_funct_1(esk3_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_14,plain,
    ( k1_funct_1(X1,esk4_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( esk4_4(esk3_0,X1,k9_relat_1(esk3_0,X1),k1_funct_1(esk3_0,X2)) = X2
    | ~ r2_hidden(esk4_4(esk3_0,X1,k9_relat_1(esk3_0,X1),k1_funct_1(esk3_0,X2)),k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,X2),k9_relat_1(esk3_0,X1))
    | ~ r2_hidden(X2,k1_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10]),c_0_11])])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r1_tarski(X23,X24)
        | ~ r2_hidden(X25,X23)
        | r2_hidden(X25,X24) )
      & ( r2_hidden(esk7_2(X26,X27),X26)
        | r1_tarski(X26,X27) )
      & ( ~ r2_hidden(esk7_2(X26,X27),X27)
        | r1_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk4_4(esk3_0,X1,k9_relat_1(esk3_0,X1),k1_funct_1(esk3_0,X2)) = X2
    | ~ r2_hidden(k1_funct_1(esk3_0,X2),k9_relat_1(esk3_0,X1))
    | ~ r2_hidden(X2,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_10]),c_0_11])])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k1_funct_1(esk3_0,X1),k9_relat_1(esk3_0,X2))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_10]),c_0_11])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk3_0,esk2_0))
    | ~ r2_hidden(X1,k9_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,X1),k9_relat_1(esk3_0,esk1_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_10]),c_0_11])]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r2_hidden(esk7_2(X1,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
