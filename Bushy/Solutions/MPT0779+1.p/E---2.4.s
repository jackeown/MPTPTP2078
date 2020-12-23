%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t28_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  97 expanded)
%              Number of clauses        :   16 (  42 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 280 expanded)
%              Number of equality atoms :   20 (  94 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X1),X1) = k2_wellord1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t28_wellord1.p',t28_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t28_wellord1.p',dt_k2_wellord1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t28_wellord1.p',d6_wellord1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t28_wellord1.p',d4_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X1),X1) = k2_wellord1(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t28_wellord1])).

fof(c_0_5,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | v1_relat_1(k2_wellord1(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k2_wellord1(k2_wellord1(esk2_0,esk1_0),esk1_0) != k2_wellord1(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | k2_wellord1(X28,X29) = k3_xboole_0(X28,k2_zfmisc_1(X29,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_8,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k3_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk5_3(X24,X25,X26),X24)
        | ~ r2_hidden(esk5_3(X24,X25,X26),X25)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X24)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X25)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k3_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_11,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k3_xboole_0(k2_wellord1(esk2_0,X1),k2_zfmisc_1(X2,X2)) = k2_wellord1(k2_wellord1(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk2_0,esk1_0),esk1_0) != k2_wellord1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( X1 = k2_wellord1(k2_wellord1(esk2_0,X2),X3)
    | r2_hidden(esk5_3(k2_wellord1(esk2_0,X2),k2_zfmisc_1(X3,X3),X1),k2_wellord1(esk2_0,X2))
    | r2_hidden(esk5_3(k2_wellord1(esk2_0,X2),k2_zfmisc_1(X3,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_zfmisc_1(X1,X1)) = k2_wellord1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_20,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk5_3(k2_wellord1(esk2_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0),k2_wellord1(esk2_0,esk1_0)),k2_wellord1(esk2_0,esk1_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X2))
    | ~ r2_hidden(X1,k2_wellord1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk5_3(k2_wellord1(esk2_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0),k2_wellord1(esk2_0,esk1_0)),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14]),c_0_21])]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
