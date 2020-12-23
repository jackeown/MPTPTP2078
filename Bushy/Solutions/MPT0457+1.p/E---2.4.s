%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t45_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:02 EDT 2019

% Result     : Theorem 207.92s
% Output     : CNFRefutation 207.92s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 ( 172 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t45_relat_1.p',d5_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t45_relat_1.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t45_relat_1.p',dt_k5_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t45_relat_1.p',d3_tarski)).

fof(t45_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t45_relat_1.p',t45_relat_1)).

fof(c_0_5,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(esk4_3(X17,X18,X19),X19),X17)
        | X18 != k2_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X22,X21),X17)
        | r2_hidden(X21,X18)
        | X18 != k2_relat_1(X17) )
      & ( ~ r2_hidden(esk5_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(X26,esk5_2(X23,X24)),X23)
        | X24 = k2_relat_1(X23) )
      & ( r2_hidden(esk5_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk6_2(X23,X24),esk5_2(X23,X24)),X23)
        | X24 = k2_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X28,X29,X30,X31,X32,X34,X35,X36,X39] :
      ( ( r2_hidden(k4_tarski(X31,esk7_5(X28,X29,X30,X31,X32)),X28)
        | ~ r2_hidden(k4_tarski(X31,X32),X30)
        | X30 != k5_relat_1(X28,X29)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk7_5(X28,X29,X30,X31,X32),X32),X29)
        | ~ r2_hidden(k4_tarski(X31,X32),X30)
        | X30 != k5_relat_1(X28,X29)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X34,X36),X28)
        | ~ r2_hidden(k4_tarski(X36,X35),X29)
        | r2_hidden(k4_tarski(X34,X35),X30)
        | X30 != k5_relat_1(X28,X29)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(esk8_3(X28,X29,X30),esk9_3(X28,X29,X30)),X30)
        | ~ r2_hidden(k4_tarski(esk8_3(X28,X29,X30),X39),X28)
        | ~ r2_hidden(k4_tarski(X39,esk9_3(X28,X29,X30)),X29)
        | X30 = k5_relat_1(X28,X29)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk8_3(X28,X29,X30),esk10_3(X28,X29,X30)),X28)
        | r2_hidden(k4_tarski(esk8_3(X28,X29,X30),esk9_3(X28,X29,X30)),X30)
        | X30 = k5_relat_1(X28,X29)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk10_3(X28,X29,X30),esk9_3(X28,X29,X30)),X29)
        | r2_hidden(k4_tarski(esk8_3(X28,X29,X30),esk9_3(X28,X29,X30)),X30)
        | X30 = k5_relat_1(X28,X29)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X29)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X41)
      | ~ v1_relat_1(X42)
      | v1_relat_1(k5_relat_1(X41,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),esk3_2(k2_relat_1(X1),X2)),esk3_2(k2_relat_1(X1),X2)),X1)
    | r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t45_relat_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk7_5(X1,X2,k5_relat_1(X1,X2),esk4_3(k5_relat_1(X1,X2),k2_relat_1(k5_relat_1(X1,X2)),esk3_2(k2_relat_1(k5_relat_1(X1,X2)),X3)),esk3_2(k2_relat_1(k5_relat_1(X1,X2)),X3)),esk3_2(k2_relat_1(k5_relat_1(X1,X2)),X3)),X2)
    | r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k2_relat_1(k5_relat_1(esk1_0,esk2_0)),k2_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_2(k2_relat_1(k5_relat_1(X1,X2)),X3),k2_relat_1(X2))
    | r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(esk1_0,esk2_0)),k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
