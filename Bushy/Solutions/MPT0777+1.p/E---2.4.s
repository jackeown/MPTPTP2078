%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t26_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  30 expanded)
%              Number of clauses        :   10 (  12 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  51 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t26_wellord1.p',t16_xboole_1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t26_wellord1.p',d6_wellord1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t26_wellord1.p',t123_zfmisc_1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t26_wellord1.p',dt_k2_wellord1)).

fof(t26_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t26_wellord1.p',t26_wellord1)).

fof(c_0_5,plain,(
    ! [X19,X20,X21] : k3_xboole_0(k3_xboole_0(X19,X20),X21) = k3_xboole_0(X19,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | k2_wellord1(X10,X11) = k3_xboole_0(X10,k2_zfmisc_1(X11,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_7,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18] : k2_zfmisc_1(k3_xboole_0(X15,X16),k3_xboole_0(X17,X18)) = k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | v1_relat_1(k2_wellord1(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t26_wellord1])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k2_zfmisc_1(X3,X3))) = k2_wellord1(k3_xboole_0(X1,X2),X3)
    | ~ v1_relat_1(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(esk3_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))) = k2_wellord1(k2_wellord1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_13]),c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(esk3_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
