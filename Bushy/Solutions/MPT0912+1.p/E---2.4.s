%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t72_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:13 EDT 2019

% Result     : Theorem 16.64s
% Output     : CNFRefutation 16.64s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 110 expanded)
%              Number of clauses        :   32 (  52 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 505 expanded)
%              Number of equality atoms :   42 ( 173 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
        & ! [X5,X6,X7] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & r2_hidden(X7,X4)
              & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',t72_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',d3_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',d2_zfmisc_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',t7_boole)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',d3_zfmisc_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t72_mcart_1.p',t2_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
          & ! [X5,X6,X7] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & r2_hidden(X7,X4)
                & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    inference(assume_negation,[status(cth)],[t72_mcart_1])).

fof(c_0_8,negated_conjecture,(
    ! [X12,X13,X14] :
      ( r2_hidden(esk1_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))
      & ( ~ r2_hidden(X12,esk2_0)
        | ~ r2_hidden(X13,esk3_0)
        | ~ r2_hidden(X14,esk4_0)
        | esk1_0 != k3_mcart_1(X12,X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X34,X35,X36] : k3_mcart_1(X34,X35,X36) = k4_tarski(k4_tarski(X34,X35),X36) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_10,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X3,esk4_0)
    | esk1_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X17,X18,X19,X20,X23,X24,X25,X26,X27,X28,X30,X31] :
      ( ( r2_hidden(esk5_4(X17,X18,X19,X20),X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk6_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( X20 = k4_tarski(esk5_4(X17,X18,X19,X20),esk6_4(X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(X24,X17)
        | ~ r2_hidden(X25,X18)
        | X23 != k4_tarski(X24,X25)
        | r2_hidden(X23,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(esk7_3(X26,X27,X28),X28)
        | ~ r2_hidden(X30,X26)
        | ~ r2_hidden(X31,X27)
        | esk7_3(X26,X27,X28) != k4_tarski(X30,X31)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk8_3(X26,X27,X28),X26)
        | r2_hidden(esk7_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk9_3(X26,X27,X28),X27)
        | r2_hidden(esk7_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( esk7_3(X26,X27,X28) = k4_tarski(esk8_3(X26,X27,X28),esk9_3(X26,X27,X28))
        | r2_hidden(esk7_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( esk1_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X3,esk4_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k4_tarski(esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | ~ v1_xboole_0(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(X1,X2) != esk1_0
    | X3 != k2_zfmisc_1(X4,X5)
    | ~ r2_hidden(esk6_4(X4,X5,X3,X1),esk3_0)
    | ~ r2_hidden(esk5_4(X4,X5,X3,X1),esk2_0)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X37,X38,X39] : k3_zfmisc_1(X37,X38,X39) = k2_zfmisc_1(k2_zfmisc_1(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | m1_subset_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(X1,X2) != esk1_0
    | X3 != k2_zfmisc_1(X4,esk3_0)
    | ~ r2_hidden(esk5_4(X4,esk3_0,X3,X1),esk2_0)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( X1 != k2_zfmisc_1(esk2_0,esk3_0)
    | k4_tarski(X2,X3) != esk1_0
    | ~ r2_hidden(X3,esk4_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

fof(c_0_28,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X44,X45)
      | v1_xboole_0(X45)
      | r2_hidden(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),X1)
    | X3 != k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(X1,X2) != esk1_0
    | ~ r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X2,esk4_0) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(X1,X2) != esk1_0
    | ~ m1_subset_1(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X2,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_4(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk1_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk6_4(X1,X2,X3,X4),X2)
    | X3 != k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_39,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(esk5_4(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk1_0),X1) != esk1_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk6_4(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk1_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_14]),c_0_30])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk6_4(k2_zfmisc_1(esk2_0,esk3_0),esk4_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk1_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_44])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
