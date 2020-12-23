%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 360 expanded)
%              Number of clauses        :   58 ( 157 expanded)
%              Number of leaves         :   18 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  230 ( 743 expanded)
%              Number of equality atoms :   56 ( 215 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t162_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t159_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k9_relat_1(k5_relat_1(X2,X3),X1) = k9_relat_1(X3,k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(c_0_18,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X7,X8),X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t162_relat_1])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & r1_tarski(esk5_0,esk6_0)
    & k9_relat_1(k7_relat_1(esk4_0,esk6_0),esk5_0) != k9_relat_1(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_24,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ r1_tarski(k1_relat_1(X43),X42)
      | k7_relat_1(X43,X42) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_25,plain,(
    ! [X32] :
      ( k1_relat_1(k6_relat_1(X32)) = X32
      & k2_relat_1(k6_relat_1(X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_26,plain,(
    ! [X20] : v1_relat_1(k6_relat_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X35,X36,X37] :
      ( ( r2_hidden(X35,X36)
        | ~ r2_hidden(X35,k1_relat_1(k7_relat_1(X37,X36)))
        | ~ v1_relat_1(X37) )
      & ( r2_hidden(X35,k1_relat_1(X37))
        | ~ r2_hidden(X35,k1_relat_1(k7_relat_1(X37,X36)))
        | ~ v1_relat_1(X37) )
      & ( ~ r2_hidden(X35,X36)
        | ~ r2_hidden(X35,k1_relat_1(X37))
        | r2_hidden(X35,k1_relat_1(k7_relat_1(X37,X36)))
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_30,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(k1_relat_1(k7_relat_1(X39,X38)),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_36,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | v1_relat_1(k7_relat_1(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_37,plain,(
    ! [X44] :
      ( ~ v1_relat_1(X44)
      | k7_relat_1(X44,k1_relat_1(X44)) = X44 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_40,plain,(
    ! [X12,X13,X16,X18,X19] :
      ( ( ~ v1_relat_1(X12)
        | ~ r2_hidden(X13,X12)
        | X13 = k4_tarski(esk1_2(X12,X13),esk2_2(X12,X13)) )
      & ( r2_hidden(esk3_1(X16),X16)
        | v1_relat_1(X16) )
      & ( esk3_1(X16) != k4_tarski(X18,X19)
        | v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k7_relat_1(X1,esk6_0) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31]),c_0_32])])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_49,plain,(
    ! [X33,X34] :
      ( ( r1_tarski(k5_relat_1(X34,k6_relat_1(X33)),X34)
        | ~ v1_relat_1(X34) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X33),X34),X34)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_50,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k2_relat_1(k7_relat_1(X25,X24)) = k9_relat_1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk5_0),esk6_0) = k7_relat_1(X1,esk5_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_52,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_32])])).

cnf(c_0_53,plain,
    ( v1_relat_1(X1)
    | esk3_1(X1) != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( X2 = k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( r2_hidden(esk3_1(X1),X2)
    | v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_48])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | k7_relat_1(X41,X40) = k5_relat_1(k6_relat_1(X40),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_59,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | ~ r1_tarski(X27,X28)
      | r1_tarski(k9_relat_1(X27,X26),k9_relat_1(X28,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

cnf(c_0_60,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk5_0),esk6_0) = k6_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_32])])).

cnf(c_0_62,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(esk3_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_64,plain,
    ( r2_hidden(esk3_1(X1),k2_xboole_0(X1,X2))
    | v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k5_relat_1(X2,k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_57])).

cnf(c_0_66,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk5_0),esk6_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_32])])).

cnf(c_0_69,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k6_relat_1(X2))
    | ~ r1_tarski(X1,k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_32]),c_0_32])])).

fof(c_0_71,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k9_relat_1(X23,k1_relat_1(X23)) = k2_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk6_0),esk5_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k6_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_32])])).

fof(c_0_74,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v1_relat_1(X31)
      | k9_relat_1(k5_relat_1(X30,X31),X29) = k9_relat_1(X31,k9_relat_1(X30,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).

cnf(c_0_75,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_22])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,k6_relat_1(esk6_0))
    | ~ r1_tarski(X1,k6_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_61])).

cnf(c_0_77,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(X1,esk6_0) = esk5_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,k9_relat_1(X1,esk6_0))
    | ~ r1_tarski(X1,k6_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( k9_relat_1(k5_relat_1(X1,X2),X3) = k9_relat_1(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k6_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_32])])).

cnf(c_0_81,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_31]),c_0_62]),c_0_32])])).

cnf(c_0_82,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_66]),c_0_32]),c_0_32])])).

cnf(c_0_83,negated_conjecture,
    ( k7_relat_1(k6_relat_1(X1),esk6_0) = k6_relat_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_32])])).

cnf(c_0_84,negated_conjecture,
    ( k9_relat_1(X1,k9_relat_1(X2,esk6_0)) = esk5_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(esk5_0,k9_relat_1(X1,k9_relat_1(X2,esk6_0)))
    | ~ r1_tarski(k5_relat_1(X2,X1),k6_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_81]),c_0_32])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k6_relat_1(X1),k6_relat_1(esk6_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k9_relat_1(k6_relat_1(X1),esk5_0) = esk5_0
    | ~ r1_tarski(esk5_0,k9_relat_1(k6_relat_1(X1),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_57]),c_0_68]),c_0_32]),c_0_32]),c_0_68])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(X1,k9_relat_1(k6_relat_1(esk6_0),X1))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_32])])).

cnf(c_0_89,plain,
    ( k9_relat_1(X1,k9_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_66]),c_0_32])])).

cnf(c_0_90,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk6_0),esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_48])])).

cnf(c_0_91,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,esk6_0),esk5_0) != k9_relat_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_92,negated_conjecture,
    ( k9_relat_1(k7_relat_1(X1,esk6_0),esk5_0) = k9_relat_1(X1,esk5_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.028 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.19/0.48  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.48  fof(t162_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.19/0.48  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.19/0.48  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.48  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.19/0.48  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.19/0.48  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.19/0.48  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.19/0.48  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.48  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.48  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.48  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.48  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 0.19/0.48  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.48  fof(t159_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k9_relat_1(k5_relat_1(X2,X3),X1)=k9_relat_1(X3,k9_relat_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 0.19/0.48  fof(c_0_18, plain, ![X7, X8, X9]:(~r1_tarski(k2_xboole_0(X7,X8),X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.19/0.48  fof(c_0_19, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.48  fof(c_0_20, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)))), inference(assume_negation,[status(cth)],[t162_relat_1])).
% 0.19/0.48  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  fof(c_0_23, negated_conjecture, (v1_relat_1(esk4_0)&(r1_tarski(esk5_0,esk6_0)&k9_relat_1(k7_relat_1(esk4_0,esk6_0),esk5_0)!=k9_relat_1(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.48  fof(c_0_24, plain, ![X42, X43]:(~v1_relat_1(X43)|(~r1_tarski(k1_relat_1(X43),X42)|k7_relat_1(X43,X42)=X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.19/0.48  fof(c_0_25, plain, ![X32]:(k1_relat_1(k6_relat_1(X32))=X32&k2_relat_1(k6_relat_1(X32))=X32), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.48  fof(c_0_26, plain, ![X20]:v1_relat_1(k6_relat_1(X20)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.19/0.48  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.48  cnf(c_0_28, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.48  fof(c_0_29, plain, ![X35, X36, X37]:(((r2_hidden(X35,X36)|~r2_hidden(X35,k1_relat_1(k7_relat_1(X37,X36)))|~v1_relat_1(X37))&(r2_hidden(X35,k1_relat_1(X37))|~r2_hidden(X35,k1_relat_1(k7_relat_1(X37,X36)))|~v1_relat_1(X37)))&(~r2_hidden(X35,X36)|~r2_hidden(X35,k1_relat_1(X37))|r2_hidden(X35,k1_relat_1(k7_relat_1(X37,X36)))|~v1_relat_1(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.19/0.48  cnf(c_0_30, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  cnf(c_0_31, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.48  cnf(c_0_32, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  fof(c_0_33, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.48  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,esk6_0)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.48  fof(c_0_35, plain, ![X38, X39]:(~v1_relat_1(X39)|r1_tarski(k1_relat_1(k7_relat_1(X39,X38)),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.19/0.48  fof(c_0_36, plain, ![X21, X22]:(~v1_relat_1(X21)|v1_relat_1(k7_relat_1(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.19/0.48  fof(c_0_37, plain, ![X44]:(~v1_relat_1(X44)|k7_relat_1(X44,k1_relat_1(X44))=X44), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.19/0.48  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_39, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.48  fof(c_0_40, plain, ![X12, X13, X16, X18, X19]:((~v1_relat_1(X12)|(~r2_hidden(X13,X12)|X13=k4_tarski(esk1_2(X12,X13),esk2_2(X12,X13))))&((r2_hidden(esk3_1(X16),X16)|v1_relat_1(X16))&(esk3_1(X16)!=k4_tarski(X18,X19)|v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.48  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.48  cnf(c_0_42, negated_conjecture, (k7_relat_1(X1,esk6_0)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_34])).
% 0.19/0.48  cnf(c_0_43, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.48  cnf(c_0_44, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.48  cnf(c_0_45, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_31]), c_0_32])])).
% 0.19/0.48  cnf(c_0_47, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.48  fof(c_0_49, plain, ![X33, X34]:((r1_tarski(k5_relat_1(X34,k6_relat_1(X33)),X34)|~v1_relat_1(X34))&(r1_tarski(k5_relat_1(k6_relat_1(X33),X34),X34)|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.19/0.48  fof(c_0_50, plain, ![X24, X25]:(~v1_relat_1(X25)|k2_relat_1(k7_relat_1(X25,X24))=k9_relat_1(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.48  cnf(c_0_51, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk5_0),esk6_0)=k7_relat_1(X1,esk5_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.19/0.48  cnf(c_0_52, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_31]), c_0_32])])).
% 0.19/0.48  cnf(c_0_53, plain, (v1_relat_1(X1)|esk3_1(X1)!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  cnf(c_0_54, plain, (X2=k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  cnf(c_0_55, plain, (r2_hidden(esk3_1(X1),X2)|v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.48  cnf(c_0_56, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_21, c_0_48])).
% 0.19/0.48  cnf(c_0_57, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.48  fof(c_0_58, plain, ![X40, X41]:(~v1_relat_1(X41)|k7_relat_1(X41,X40)=k5_relat_1(k6_relat_1(X40),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.48  fof(c_0_59, plain, ![X26, X27, X28]:(~v1_relat_1(X27)|(~v1_relat_1(X28)|(~r1_tarski(X27,X28)|r1_tarski(k9_relat_1(X27,X26),k9_relat_1(X28,X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.19/0.48  cnf(c_0_60, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.48  cnf(c_0_61, negated_conjecture, (k7_relat_1(k6_relat_1(esk5_0),esk6_0)=k6_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_32])])).
% 0.19/0.48  cnf(c_0_62, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.48  cnf(c_0_63, plain, (v1_relat_1(X1)|~r2_hidden(esk3_1(X1),X2)|~v1_relat_1(X2)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54])])).
% 0.19/0.48  cnf(c_0_64, plain, (r2_hidden(esk3_1(X1),k2_xboole_0(X1,X2))|v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.48  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k5_relat_1(X2,k6_relat_1(X3)))), inference(spm,[status(thm)],[c_0_27, c_0_57])).
% 0.19/0.48  cnf(c_0_66, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.48  cnf(c_0_67, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.48  cnf(c_0_68, negated_conjecture, (k9_relat_1(k6_relat_1(esk5_0),esk6_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_32])])).
% 0.19/0.48  cnf(c_0_69, plain, (v1_relat_1(X1)|~v1_relat_1(k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.48  cnf(c_0_70, plain, (r1_tarski(X1,k6_relat_1(X2))|~r1_tarski(X1,k7_relat_1(k6_relat_1(X3),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_32]), c_0_32])])).
% 0.19/0.48  fof(c_0_71, plain, ![X23]:(~v1_relat_1(X23)|k9_relat_1(X23,k1_relat_1(X23))=k2_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.48  cnf(c_0_72, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.48  cnf(c_0_73, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk6_0),esk5_0)|~v1_relat_1(X1)|~r1_tarski(X1,k6_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_32])])).
% 0.19/0.48  fof(c_0_74, plain, ![X29, X30, X31]:(~v1_relat_1(X30)|(~v1_relat_1(X31)|k9_relat_1(k5_relat_1(X30,X31),X29)=k9_relat_1(X31,k9_relat_1(X30,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).
% 0.19/0.48  cnf(c_0_75, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_22])).
% 0.19/0.48  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,k6_relat_1(esk6_0))|~r1_tarski(X1,k6_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_70, c_0_61])).
% 0.19/0.48  cnf(c_0_77, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.48  cnf(c_0_78, negated_conjecture, (k9_relat_1(X1,esk6_0)=esk5_0|~v1_relat_1(X1)|~r1_tarski(esk5_0,k9_relat_1(X1,esk6_0))|~r1_tarski(X1,k6_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.48  cnf(c_0_79, plain, (k9_relat_1(k5_relat_1(X1,X2),X3)=k9_relat_1(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (v1_relat_1(X1)|~r1_tarski(X1,k6_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_32])])).
% 0.19/0.48  cnf(c_0_81, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_31]), c_0_62]), c_0_32])])).
% 0.19/0.48  cnf(c_0_82, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_66]), c_0_32]), c_0_32])])).
% 0.19/0.48  cnf(c_0_83, negated_conjecture, (k7_relat_1(k6_relat_1(X1),esk6_0)=k6_relat_1(X1)|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_31]), c_0_32])])).
% 0.19/0.48  cnf(c_0_84, negated_conjecture, (k9_relat_1(X1,k9_relat_1(X2,esk6_0))=esk5_0|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(esk5_0,k9_relat_1(X1,k9_relat_1(X2,esk6_0)))|~r1_tarski(k5_relat_1(X2,X1),k6_relat_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.19/0.48  cnf(c_0_85, plain, (r1_tarski(X1,k9_relat_1(X2,X1))|~v1_relat_1(X2)|~r1_tarski(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_81]), c_0_32])])).
% 0.19/0.48  cnf(c_0_86, negated_conjecture, (r1_tarski(k6_relat_1(X1),k6_relat_1(esk6_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (k9_relat_1(k6_relat_1(X1),esk5_0)=esk5_0|~r1_tarski(esk5_0,k9_relat_1(k6_relat_1(X1),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_57]), c_0_68]), c_0_32]), c_0_32]), c_0_68])])).
% 0.19/0.48  cnf(c_0_88, negated_conjecture, (r1_tarski(X1,k9_relat_1(k6_relat_1(esk6_0),X1))|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_32])])).
% 0.19/0.48  cnf(c_0_89, plain, (k9_relat_1(X1,k9_relat_1(k6_relat_1(X2),X3))=k9_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_66]), c_0_32])])).
% 0.19/0.48  cnf(c_0_90, negated_conjecture, (k9_relat_1(k6_relat_1(esk6_0),esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_48])])).
% 0.19/0.48  cnf(c_0_91, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,esk6_0),esk5_0)!=k9_relat_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.48  cnf(c_0_92, negated_conjecture, (k9_relat_1(k7_relat_1(X1,esk6_0),esk5_0)=k9_relat_1(X1,esk5_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.48  cnf(c_0_93, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.48  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 95
% 0.19/0.48  # Proof object clause steps            : 58
% 0.19/0.48  # Proof object formula steps           : 37
% 0.19/0.48  # Proof object conjectures             : 23
% 0.19/0.48  # Proof object clause conjectures      : 20
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 24
% 0.19/0.48  # Proof object initial formulas used   : 18
% 0.19/0.48  # Proof object generating inferences   : 33
% 0.19/0.48  # Proof object simplifying inferences  : 46
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 18
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 28
% 0.19/0.48  # Removed in clause preprocessing      : 0
% 0.19/0.48  # Initial clauses in saturation        : 28
% 0.19/0.48  # Processed clauses                    : 1316
% 0.19/0.48  # ...of these trivial                  : 5
% 0.19/0.48  # ...subsumed                          : 835
% 0.19/0.48  # ...remaining for further processing  : 476
% 0.19/0.48  # Other redundant clauses eliminated   : 3
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 14
% 0.19/0.48  # Backward-rewritten                   : 27
% 0.19/0.48  # Generated clauses                    : 5261
% 0.19/0.48  # ...of the previous two non-trivial   : 4798
% 0.19/0.48  # Contextual simplify-reflections      : 40
% 0.19/0.48  # Paramodulations                      : 5258
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 3
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 406
% 0.19/0.48  #    Positive orientable unit clauses  : 25
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 2
% 0.19/0.48  #    Non-unit-clauses                  : 379
% 0.19/0.48  # Current number of unprocessed clauses: 3512
% 0.19/0.48  # ...number of literals in the above   : 12258
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 68
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 30356
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 19599
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 754
% 0.19/0.48  # Unit Clause-clause subsumption calls : 120
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 17
% 0.19/0.48  # BW rewrite match successes           : 7
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 78393
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.137 s
% 0.19/0.48  # System time              : 0.005 s
% 0.19/0.48  # Total time               : 0.142 s
% 0.19/0.48  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
