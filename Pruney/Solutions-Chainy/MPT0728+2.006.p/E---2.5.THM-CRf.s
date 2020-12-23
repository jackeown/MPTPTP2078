%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:02 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  120 (5257 expanded)
%              Number of clauses        :   89 (2422 expanded)
%              Number of leaves         :   15 (1417 expanded)
%              Depth                    :   22
%              Number of atoms          :  220 (11157 expanded)
%              Number of equality atoms :   39 (3611 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(t10_ordinal1,conjecture,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_15,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,X35)
        | ~ r1_tarski(k2_tarski(X33,X34),X35) )
      & ( r2_hidden(X34,X35)
        | ~ r1_tarski(k2_tarski(X33,X34),X35) )
      & ( ~ r2_hidden(X33,X35)
        | ~ r2_hidden(X34,X35)
        | r1_tarski(k2_tarski(X33,X34),X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ r1_tarski(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X2),X2),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X1))
    | ~ r2_hidden(X2,k3_enumset1(X3,X3,X3,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X3),X3)),k3_enumset1(X2,X2,X2,X2,X3))
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_43,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X13)
        | r2_hidden(X11,X12)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X1),X1)),k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_42])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X1),X1)) = k3_enumset1(X2,X2,X2,X2,X1)
    | ~ r1_tarski(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X1),X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1)) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X1),X2))
    | ~ r2_hidden(X3,k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_50])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_51])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3))
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_37])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X2),X2),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3))
    | r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X2),X2),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_63,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_64,plain,(
    ! [X36,X37] : k1_setfam_1(k2_tarski(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)
    | r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_34])).

cnf(c_0_68,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X3))
    | ~ r2_hidden(X2,k3_enumset1(X1,X1,X1,X1,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

fof(c_0_69,plain,(
    ! [X19,X20] : k3_xboole_0(X19,X20) = k5_xboole_0(k5_xboole_0(X19,X20),k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_70,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_72,plain,(
    ! [X16,X17,X18] : r1_tarski(k3_xboole_0(X16,X17),k2_xboole_0(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1))
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),k5_xboole_0(X2,k3_enumset1(X4,X4,X4,X4,X1)))
    | ~ r2_hidden(X3,k5_xboole_0(X2,k3_enumset1(X4,X4,X4,X4,X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_67])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2)),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_59])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_70,c_0_23])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_71,c_0_23])).

cnf(c_0_80,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_73]),c_0_39])])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_67])).

cnf(c_0_84,plain,
    ( k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2)) = k3_enumset1(X1,X1,X1,X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_75])).

cnf(c_0_85,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_76])).

cnf(c_0_86,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_78]),c_0_79]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_88,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_81]),c_0_82])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3))
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X4)))
    | r2_hidden(X4,X2)
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X4,X4)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_83])).

cnf(c_0_91,plain,
    ( k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2)) = k3_enumset1(X1,X1,X1,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_92,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_86])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X4))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_87])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),X4))
    | r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_95,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_88])).

cnf(c_0_96,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_59])).

cnf(c_0_97,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)
    | r2_hidden(X3,k5_xboole_0(X2,k3_enumset1(X4,X4,X4,X4,X1)))
    | ~ r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_91]),c_0_46]),c_0_91])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k5_xboole_0(X3,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_46]),c_0_93])).

cnf(c_0_99,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)
    | r2_hidden(X3,k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X1),X2))
    | ~ r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_91]),c_0_91]),c_0_46]),c_0_51])).

fof(c_0_100,negated_conjecture,(
    ~ ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(assume_negation,[status(cth)],[t10_ordinal1])).

fof(c_0_101,plain,(
    ! [X38] : k1_ordinal1(X38) = k2_xboole_0(X38,k1_tarski(X38)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_102,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_95]),c_0_96])])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))
    | r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2) ),
    inference(spm,[status(thm)],[c_0_97,c_0_34])).

cnf(c_0_105,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_46])).

cnf(c_0_106,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),X3))
    | r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X3) ),
    inference(spm,[status(thm)],[c_0_99,c_0_34])).

fof(c_0_107,negated_conjecture,(
    ~ r2_hidden(esk2_0,k1_ordinal1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_100])])])).

cnf(c_0_108,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_109,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_110,plain,
    ( r2_hidden(X1,k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_111,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,esk1_2(k3_enumset1(X3,X3,X3,X3,X3),X3)))
    | ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_91])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_ordinal1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_114,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,plain,
    ( r2_hidden(X1,k5_xboole_0(k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X1)),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_110])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_46])).

cnf(c_0_117,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114]),c_0_23]),c_0_78]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X1)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_86]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_118])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.19/1.37  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.19/1.37  # and selection function SelectNegativeLiterals.
% 1.19/1.37  #
% 1.19/1.37  # Preprocessing time       : 0.027 s
% 1.19/1.37  # Presaturation interreduction done
% 1.19/1.37  
% 1.19/1.37  # Proof found!
% 1.19/1.37  # SZS status Theorem
% 1.19/1.37  # SZS output start CNFRefutation
% 1.19/1.37  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.19/1.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.19/1.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.19/1.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.19/1.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.19/1.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.19/1.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.19/1.37  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 1.19/1.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.19/1.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.19/1.37  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 1.19/1.37  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.19/1.37  fof(t10_ordinal1, conjecture, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.19/1.37  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.19/1.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.19/1.37  fof(c_0_15, plain, ![X33, X34, X35]:(((r2_hidden(X33,X35)|~r1_tarski(k2_tarski(X33,X34),X35))&(r2_hidden(X34,X35)|~r1_tarski(k2_tarski(X33,X34),X35)))&(~r2_hidden(X33,X35)|~r2_hidden(X34,X35)|r1_tarski(k2_tarski(X33,X34),X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 1.19/1.37  fof(c_0_16, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.19/1.37  fof(c_0_17, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.19/1.37  fof(c_0_18, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.19/1.37  fof(c_0_19, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.19/1.37  fof(c_0_20, plain, ![X39, X40]:(~r2_hidden(X39,X40)|~r1_tarski(X40,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 1.19/1.37  fof(c_0_21, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.19/1.37  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.19/1.37  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.19/1.37  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.19/1.37  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.19/1.37  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.19/1.37  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.19/1.37  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.19/1.37  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])).
% 1.19/1.37  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 1.19/1.37  cnf(c_0_31, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.19/1.37  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.19/1.37  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.19/1.37  cnf(c_0_34, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.19/1.37  cnf(c_0_35, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_23]), c_0_24]), c_0_25])).
% 1.19/1.37  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_23]), c_0_24]), c_0_25])).
% 1.19/1.37  cnf(c_0_37, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X2),X2),k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.19/1.37  cnf(c_0_38, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X1))|~r2_hidden(X2,k3_enumset1(X3,X3,X3,X3,X1))), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 1.19/1.37  cnf(c_0_39, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 1.19/1.37  cnf(c_0_40, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X3),X3)),k3_enumset1(X2,X2,X2,X2,X3))|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3))), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 1.19/1.37  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.19/1.37  cnf(c_0_42, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.19/1.37  fof(c_0_43, plain, ![X11, X12, X13]:(((~r2_hidden(X11,X12)|~r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13)))&(r2_hidden(X11,X12)|r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13))))&((~r2_hidden(X11,X12)|r2_hidden(X11,X13)|r2_hidden(X11,k5_xboole_0(X12,X13)))&(~r2_hidden(X11,X13)|r2_hidden(X11,X12)|r2_hidden(X11,k5_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 1.19/1.37  cnf(c_0_44, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X1),X1)),k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 1.19/1.37  cnf(c_0_45, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 1.19/1.37  cnf(c_0_46, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_42])])).
% 1.19/1.37  cnf(c_0_47, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.19/1.37  cnf(c_0_48, plain, (k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X1),X1))=k3_enumset1(X2,X2,X2,X2,X1)|~r1_tarski(k3_enumset1(X2,X2,X2,X2,X1),k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X1),X1)))), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 1.19/1.37  cnf(c_0_49, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.19/1.37  cnf(c_0_50, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 1.19/1.37  cnf(c_0_51, plain, (k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1))=k3_enumset1(X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.19/1.37  cnf(c_0_52, plain, (r2_hidden(X1,X2)|r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X1),X2))|~r2_hidden(X3,k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X1),X2))), inference(spm,[status(thm)],[c_0_35, c_0_50])).
% 1.19/1.37  cnf(c_0_53, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.19/1.37  cnf(c_0_54, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(spm,[status(thm)],[c_0_29, c_0_51])).
% 1.19/1.37  cnf(c_0_55, plain, (r2_hidden(X1,X2)|r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X1),X2))), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 1.19/1.37  cnf(c_0_56, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3))|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X3))), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 1.19/1.37  cnf(c_0_57, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.19/1.37  cnf(c_0_58, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.19/1.37  cnf(c_0_59, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_56, c_0_37])).
% 1.19/1.37  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 1.19/1.37  cnf(c_0_61, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X2),X2),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3))|r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X2),X2),X3)), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 1.19/1.37  cnf(c_0_62, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.19/1.37  fof(c_0_63, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.19/1.37  fof(c_0_64, plain, ![X36, X37]:k1_setfam_1(k2_tarski(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.19/1.37  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.19/1.37  cnf(c_0_66, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)|r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.19/1.37  cnf(c_0_67, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_34])).
% 1.19/1.37  cnf(c_0_68, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X3))|~r2_hidden(X2,k3_enumset1(X1,X1,X1,X1,X3))), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 1.19/1.37  fof(c_0_69, plain, ![X19, X20]:k3_xboole_0(X19,X20)=k5_xboole_0(k5_xboole_0(X19,X20),k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 1.19/1.37  cnf(c_0_70, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.19/1.37  cnf(c_0_71, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.19/1.37  fof(c_0_72, plain, ![X16, X17, X18]:r1_tarski(k3_xboole_0(X16,X17),k2_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 1.19/1.37  cnf(c_0_73, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1))|r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.19/1.37  cnf(c_0_74, plain, (r2_hidden(X1,X2)|r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),k5_xboole_0(X2,k3_enumset1(X4,X4,X4,X4,X1)))|~r2_hidden(X3,k5_xboole_0(X2,k3_enumset1(X4,X4,X4,X4,X1)))), inference(spm,[status(thm)],[c_0_35, c_0_67])).
% 1.19/1.37  cnf(c_0_75, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2)),k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_68, c_0_59])).
% 1.19/1.37  cnf(c_0_76, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1)))), inference(spm,[status(thm)],[c_0_60, c_0_34])).
% 1.19/1.37  cnf(c_0_77, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.19/1.37  cnf(c_0_78, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_70, c_0_23])).
% 1.19/1.37  cnf(c_0_79, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_71, c_0_23])).
% 1.19/1.37  cnf(c_0_80, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.19/1.37  cnf(c_0_81, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_73]), c_0_39])])).
% 1.19/1.37  cnf(c_0_82, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 1.19/1.37  cnf(c_0_83, plain, (r2_hidden(X1,X2)|r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))), inference(spm,[status(thm)],[c_0_74, c_0_67])).
% 1.19/1.37  cnf(c_0_84, plain, (k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2))=k3_enumset1(X1,X1,X1,X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2)))), inference(spm,[status(thm)],[c_0_41, c_0_75])).
% 1.19/1.37  cnf(c_0_85, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2)))), inference(spm,[status(thm)],[c_0_68, c_0_76])).
% 1.19/1.37  cnf(c_0_86, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 1.19/1.37  cnf(c_0_87, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_78]), c_0_79]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 1.19/1.37  cnf(c_0_88, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_81]), c_0_82])).
% 1.19/1.37  cnf(c_0_89, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X3))|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X2))), inference(spm,[status(thm)],[c_0_53, c_0_42])).
% 1.19/1.37  cnf(c_0_90, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X4)))|r2_hidden(X4,X2)|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X4,X4))), inference(spm,[status(thm)],[c_0_53, c_0_83])).
% 1.19/1.37  cnf(c_0_91, plain, (k3_enumset1(X1,X1,X1,X1,esk1_2(k3_enumset1(X2,X2,X2,X2,X2),X2))=k3_enumset1(X1,X1,X1,X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 1.19/1.37  cnf(c_0_92, plain, (~r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_57, c_0_86])).
% 1.19/1.37  cnf(c_0_93, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X4)))), inference(spm,[status(thm)],[c_0_53, c_0_87])).
% 1.19/1.37  cnf(c_0_94, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),X4))|r2_hidden(X3,X4)|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X3))), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 1.19/1.37  cnf(c_0_95, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X1))), inference(spm,[status(thm)],[c_0_54, c_0_88])).
% 1.19/1.37  cnf(c_0_96, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_89, c_0_59])).
% 1.19/1.37  cnf(c_0_97, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)|r2_hidden(X3,k5_xboole_0(X2,k3_enumset1(X4,X4,X4,X4,X1)))|~r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_91]), c_0_46]), c_0_91])).
% 1.19/1.37  cnf(c_0_98, plain, (~r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k5_xboole_0(X3,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_46]), c_0_93])).
% 1.19/1.37  cnf(c_0_99, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)|r2_hidden(X3,k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X1),X2))|~r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_91]), c_0_91]), c_0_46]), c_0_51])).
% 1.19/1.37  fof(c_0_100, negated_conjecture, ~(![X1]:r2_hidden(X1,k1_ordinal1(X1))), inference(assume_negation,[status(cth)],[t10_ordinal1])).
% 1.19/1.37  fof(c_0_101, plain, ![X38]:k1_ordinal1(X38)=k2_xboole_0(X38,k1_tarski(X38)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 1.19/1.37  fof(c_0_102, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.19/1.37  cnf(c_0_103, plain, (~r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_95]), c_0_96])])).
% 1.19/1.37  cnf(c_0_104, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))|r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X2)), inference(spm,[status(thm)],[c_0_97, c_0_34])).
% 1.19/1.37  cnf(c_0_105, plain, (~r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_98, c_0_46])).
% 1.19/1.37  cnf(c_0_106, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),X3))|r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1),X3)), inference(spm,[status(thm)],[c_0_99, c_0_34])).
% 1.19/1.37  fof(c_0_107, negated_conjecture, ~r2_hidden(esk2_0,k1_ordinal1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_100])])])).
% 1.19/1.37  cnf(c_0_108, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 1.19/1.37  cnf(c_0_109, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.19/1.37  cnf(c_0_110, plain, (r2_hidden(X1,k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 1.19/1.37  cnf(c_0_111, plain, (~r2_hidden(X1,k5_xboole_0(X2,esk1_2(k3_enumset1(X3,X3,X3,X3,X3),X3)))|~r2_hidden(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))), inference(spm,[status(thm)],[c_0_105, c_0_91])).
% 1.19/1.37  cnf(c_0_112, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X1)))), inference(spm,[status(thm)],[c_0_82, c_0_106])).
% 1.19/1.37  cnf(c_0_113, negated_conjecture, (~r2_hidden(esk2_0,k1_ordinal1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_107])).
% 1.19/1.37  cnf(c_0_114, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_108, c_0_109])).
% 1.19/1.37  cnf(c_0_115, plain, (r2_hidden(X1,k5_xboole_0(k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X1)),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_110])).
% 1.19/1.37  cnf(c_0_116, plain, (~r2_hidden(X1,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_46])).
% 1.19/1.37  cnf(c_0_117, negated_conjecture, (~r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114]), c_0_23]), c_0_78]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 1.19/1.37  cnf(c_0_118, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X2,X2,X2,X2,X1))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_86]), c_0_116])).
% 1.19/1.37  cnf(c_0_119, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_118])]), ['proof']).
% 1.19/1.37  # SZS output end CNFRefutation
% 1.19/1.37  # Proof object total steps             : 120
% 1.19/1.37  # Proof object clause steps            : 89
% 1.19/1.37  # Proof object formula steps           : 31
% 1.19/1.37  # Proof object conjectures             : 6
% 1.19/1.37  # Proof object clause conjectures      : 3
% 1.19/1.37  # Proof object formula conjectures     : 3
% 1.19/1.37  # Proof object initial clauses used    : 22
% 1.19/1.37  # Proof object initial formulas used   : 15
% 1.19/1.37  # Proof object generating inferences   : 55
% 1.19/1.37  # Proof object simplifying inferences  : 54
% 1.19/1.37  # Training examples: 0 positive, 0 negative
% 1.19/1.37  # Parsed axioms                        : 15
% 1.19/1.37  # Removed by relevancy pruning/SinE    : 0
% 1.19/1.37  # Initial clauses                      : 24
% 1.19/1.37  # Removed in clause preprocessing      : 7
% 1.19/1.37  # Initial clauses in saturation        : 17
% 1.19/1.37  # Processed clauses                    : 4418
% 1.19/1.37  # ...of these trivial                  : 132
% 1.19/1.37  # ...subsumed                          : 3514
% 1.19/1.37  # ...remaining for further processing  : 772
% 1.19/1.37  # Other redundant clauses eliminated   : 2
% 1.19/1.37  # Clauses deleted for lack of memory   : 0
% 1.19/1.37  # Backward-subsumed                    : 33
% 1.19/1.37  # Backward-rewritten                   : 39
% 1.19/1.37  # Generated clauses                    : 65321
% 1.19/1.37  # ...of the previous two non-trivial   : 63353
% 1.19/1.37  # Contextual simplify-reflections      : 6
% 1.19/1.37  # Paramodulations                      : 65285
% 1.19/1.37  # Factorizations                       : 34
% 1.19/1.37  # Equation resolutions                 : 2
% 1.19/1.37  # Propositional unsat checks           : 0
% 1.19/1.37  #    Propositional check models        : 0
% 1.19/1.37  #    Propositional check unsatisfiable : 0
% 1.19/1.37  #    Propositional clauses             : 0
% 1.19/1.37  #    Propositional clauses after purity: 0
% 1.19/1.37  #    Propositional unsat core size     : 0
% 1.19/1.37  #    Propositional preprocessing time  : 0.000
% 1.19/1.37  #    Propositional encoding time       : 0.000
% 1.19/1.37  #    Propositional solver time         : 0.000
% 1.19/1.37  #    Success case prop preproc time    : 0.000
% 1.19/1.37  #    Success case prop encoding time   : 0.000
% 1.19/1.37  #    Success case prop solver time     : 0.000
% 1.19/1.37  # Current number of processed clauses  : 682
% 1.19/1.37  #    Positive orientable unit clauses  : 64
% 1.19/1.37  #    Positive unorientable unit clauses: 1
% 1.19/1.37  #    Negative unit clauses             : 54
% 1.19/1.37  #    Non-unit-clauses                  : 563
% 1.19/1.37  # Current number of unprocessed clauses: 58917
% 1.19/1.37  # ...number of literals in the above   : 236127
% 1.19/1.37  # Current number of archived formulas  : 0
% 1.19/1.37  # Current number of archived clauses   : 95
% 1.19/1.37  # Clause-clause subsumption calls (NU) : 107610
% 1.19/1.37  # Rec. Clause-clause subsumption calls : 71837
% 1.19/1.37  # Non-unit clause-clause subsumptions  : 2955
% 1.19/1.37  # Unit Clause-clause subsumption calls : 4611
% 1.19/1.37  # Rewrite failures with RHS unbound    : 0
% 1.19/1.37  # BW rewrite match attempts            : 1219
% 1.19/1.37  # BW rewrite match successes           : 66
% 1.19/1.37  # Condensation attempts                : 0
% 1.19/1.37  # Condensation successes               : 0
% 1.19/1.37  # Termbank termtop insertions          : 3875465
% 1.19/1.38  
% 1.19/1.38  # -------------------------------------------------
% 1.19/1.38  # User time                : 0.986 s
% 1.19/1.38  # System time              : 0.045 s
% 1.19/1.38  # Total time               : 1.031 s
% 1.19/1.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
