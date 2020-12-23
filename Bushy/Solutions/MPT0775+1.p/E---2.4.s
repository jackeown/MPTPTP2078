%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t24_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 225.41s
% Output     : CNFRefutation 225.41s
% Verified   : 
% Statistics : Number of formulae       :   45 (  90 expanded)
%              Number of clauses        :   32 (  41 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  157 ( 428 expanded)
%              Number of equality atoms :   13 (  46 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',d4_xboole_0)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',l2_wellord1)).

fof(t24_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v8_relat_2(X2)
       => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',t24_wellord1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',t106_zfmisc_1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',d6_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',dt_k2_wellord1)).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v8_relat_2(X27)
        | ~ r2_hidden(k4_tarski(X28,X29),X27)
        | ~ r2_hidden(k4_tarski(X29,X30),X27)
        | r2_hidden(k4_tarski(X28,X30),X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk5_1(X27),esk6_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk6_1(X27),esk7_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk5_1(X27),esk7_1(X27)),X27)
        | v8_relat_2(X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v8_relat_2(X2)
         => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t24_wellord1])).

cnf(c_0_12,plain,
    ( v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk5_1(X1),esk7_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X34,X35,X36,X37] :
      ( ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( r2_hidden(X35,X37)
        | ~ r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) )
      & ( ~ r2_hidden(X34,X36)
        | ~ r2_hidden(X35,X37)
        | r2_hidden(k4_tarski(X34,X35),k2_zfmisc_1(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk6_1(X1),esk7_1(X1)),X1)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v8_relat_2(esk2_0)
    & ~ v8_relat_2(k2_wellord1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | k2_wellord1(X20,X21) = k3_xboole_0(X20,k2_zfmisc_1(X21,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_21,plain,
    ( v8_relat_2(k3_xboole_0(X1,X2))
    | ~ r2_hidden(k4_tarski(esk5_1(k3_xboole_0(X1,X2)),esk7_1(k3_xboole_0(X1,X2))),X2)
    | ~ r2_hidden(k4_tarski(esk5_1(k3_xboole_0(X1,X2)),esk7_1(k3_xboole_0(X1,X2))),X1)
    | ~ v1_relat_1(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk6_1(k3_xboole_0(X1,X2)),esk7_1(k3_xboole_0(X1,X2))),X1)
    | v8_relat_2(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk5_1(k3_xboole_0(X1,X2)),esk6_1(k3_xboole_0(X1,X2))),X2)
    | v8_relat_2(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk6_1(k3_xboole_0(X1,X2)),esk7_1(k3_xboole_0(X1,X2))),X2)
    | v8_relat_2(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ v8_relat_2(k2_wellord1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( v8_relat_2(k3_xboole_0(X1,k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(k4_tarski(esk5_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))),esk7_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3)))),X1)
    | ~ r2_hidden(esk7_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))),X3)
    | ~ r2_hidden(esk5_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))),X2)
    | ~ v1_relat_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,esk7_1(k3_xboole_0(X2,X3))),X2)
    | v8_relat_2(k3_xboole_0(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,esk6_1(k3_xboole_0(X2,X3))),X2)
    | ~ v8_relat_2(X2)
    | ~ v1_relat_1(k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(esk5_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))),X2)
    | v8_relat_2(k3_xboole_0(X1,k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(esk7_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))),X3)
    | v8_relat_2(k3_xboole_0(X1,k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk5_1(k3_xboole_0(X1,X2)),esk6_1(k3_xboole_0(X1,X2))),X1)
    | v8_relat_2(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k2_wellord1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v8_relat_2(k3_xboole_0(esk2_0,k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_39,plain,
    ( v8_relat_2(k3_xboole_0(X1,k2_zfmisc_1(X2,X3)))
    | ~ v8_relat_2(X1)
    | ~ v1_relat_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v8_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_relat_1(k3_xboole_0(esk2_0,k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_31])])).

cnf(c_0_43,plain,
    ( v1_relat_1(k3_xboole_0(X1,k2_zfmisc_1(X2,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
