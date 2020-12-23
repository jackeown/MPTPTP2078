%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t126_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:59 EDT 2019

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   47 (  75 expanded)
%              Number of clauses        :   25 (  36 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 140 expanded)
%              Number of equality atoms :   46 (  70 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t7_boole)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',d5_xboole_0)).

fof(t126_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t126_zfmisc_1)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t54_xboole_1)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t125_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',t123_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t126_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(c_0_11,plain,(
    ! [X90,X91] :
      ( ~ r2_hidden(X90,X91)
      | ~ v1_xboole_0(X91) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_12,plain,(
    ! [X89] :
      ( ~ v1_xboole_0(X89)
      | X89 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_18,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57,X58] :
      ( ( r2_hidden(X54,X51)
        | ~ r2_hidden(X54,X53)
        | X53 != k4_xboole_0(X51,X52) )
      & ( ~ r2_hidden(X54,X52)
        | ~ r2_hidden(X54,X53)
        | X53 != k4_xboole_0(X51,X52) )
      & ( ~ r2_hidden(X55,X51)
        | r2_hidden(X55,X52)
        | r2_hidden(X55,X53)
        | X53 != k4_xboole_0(X51,X52) )
      & ( ~ r2_hidden(esk12_3(X56,X57,X58),X58)
        | ~ r2_hidden(esk12_3(X56,X57,X58),X56)
        | r2_hidden(esk12_3(X56,X57,X58),X57)
        | X58 = k4_xboole_0(X56,X57) )
      & ( r2_hidden(esk12_3(X56,X57,X58),X56)
        | r2_hidden(esk12_3(X56,X57,X58),X58)
        | X58 = k4_xboole_0(X56,X57) )
      & ( ~ r2_hidden(esk12_3(X56,X57,X58),X57)
        | r2_hidden(esk12_3(X56,X57,X58),X58)
        | X58 = k4_xboole_0(X56,X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X1,X3),X2),k2_zfmisc_1(X1,k4_xboole_0(X2,X4))) ),
    inference(assume_negation,[status(cth)],[t126_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X86,X87,X88] : k4_xboole_0(X86,k3_xboole_0(X87,X88)) = k2_xboole_0(k4_xboole_0(X86,X87),k4_xboole_0(X86,X88)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

fof(c_0_21,plain,(
    ! [X74,X75,X76] :
      ( k2_zfmisc_1(k4_xboole_0(X74,X75),X76) = k4_xboole_0(k2_zfmisc_1(X74,X76),k2_zfmisc_1(X75,X76))
      & k2_zfmisc_1(X76,k4_xboole_0(X74,X75)) = k4_xboole_0(k2_zfmisc_1(X76,X74),k2_zfmisc_1(X76,X75)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk12_3(X1,X2,X3),X1)
    | r2_hidden(esk12_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X79] : k2_xboole_0(X79,k1_xboole_0) = X79 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_25,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k2_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_26,negated_conjecture,(
    k4_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(esk1_0,esk3_0),esk2_0),k2_zfmisc_1(esk1_0,k4_xboole_0(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X70,X71,X72,X73] : k2_zfmisc_1(k3_xboole_0(X70,X71),k3_xboole_0(X72,X73)) = k3_xboole_0(k2_zfmisc_1(X70,X72),k2_zfmisc_1(X71,X73)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_30,plain,(
    ! [X15,X16] : k3_xboole_0(X15,X16) = k3_xboole_0(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_31,plain,
    ( r2_hidden(esk12_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk12_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk12_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(esk1_0,esk3_0),esk2_0),k2_zfmisc_1(esk1_0,k4_xboole_0(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k4_xboole_0(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(X3,k2_zfmisc_1(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_22])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk1_0,k4_xboole_0(esk2_0,esk4_0)),k2_zfmisc_1(k4_xboole_0(esk1_0,esk3_0),esk2_0)) != k4_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(k4_xboole_0(X1,X4),X2)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_38])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_40]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
