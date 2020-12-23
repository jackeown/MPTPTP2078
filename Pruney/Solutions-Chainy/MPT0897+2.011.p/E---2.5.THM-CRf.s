%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 (91527 expanded)
%              Number of clauses        :   90 (41993 expanded)
%              Number of leaves         :   17 (23326 expanded)
%              Depth                    :   29
%              Number of atoms          :  280 (181801 expanded)
%              Number of equality atoms :  203 (132903 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t1_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t57_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(t150_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(c_0_17,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X49] :
      ( ( r2_hidden(esk2_1(X49),X49)
        | X49 = k1_xboole_0 )
      & ( r1_xboole_0(esk2_1(X49),X49)
        | X49 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X9] : k3_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_23,negated_conjecture,
    ( k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0) = k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0)
    & k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0) != k1_xboole_0
    & ( esk3_0 != esk7_0
      | esk4_0 != esk8_0
      | esk5_0 != esk9_0
      | esk6_0 != esk10_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X45,X46,X47,X48] : k4_zfmisc_1(X45,X46,X47,X48) = k2_zfmisc_1(k3_zfmisc_1(X45,X46,X47),X48) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X51,X52,X53,X54] : k4_zfmisc_1(X51,X52,X53,X54) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X51,X52),X53),X54) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0) = k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X1),X1)
    | r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X33,X34,X35,X36] :
      ( ( X33 = X35
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | k2_zfmisc_1(X33,X34) != k2_zfmisc_1(X35,X36) )
      & ( X34 = X36
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | k2_zfmisc_1(X33,X34) != k2_zfmisc_1(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk7_0,esk8_0,esk9_0),esk10_0) = k2_zfmisc_1(k3_zfmisc_1(esk3_0,esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_28])).

fof(c_0_39,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ r1_xboole_0(X29,X30)
        | r1_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X32)) )
      & ( ~ r1_xboole_0(X31,X32)
        | r1_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_xboole_0(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(k3_zfmisc_1(esk3_0,esk4_0,esk5_0),esk6_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_43,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_21])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) = k1_xboole_0
    | esk10_0 = k1_xboole_0
    | esk10_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_47]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) = k1_xboole_0
    | esk10_0 = esk6_0
    | esk10_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk10_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_52]),c_0_53]),c_0_48])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( X1 = esk10_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X2,X1) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_57]),c_0_58]),c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | esk10_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_60])).

cnf(c_0_62,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk6_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( esk10_0 = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_61]),c_0_53])])).

cnf(c_0_65,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) = X4
    | X5 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X5) != k2_zfmisc_1(X4,X6) ),
    inference(spm,[status(thm)],[c_0_62,c_0_37])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk6_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k1_xboole_0
    | k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0) != k2_zfmisc_1(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)
    | k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)
    | k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) = k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)
    | k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) = k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_71]),c_0_53])).

fof(c_0_73,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,X38)
        | ~ r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))) )
      & ( X37 != X39
        | ~ r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))) )
      & ( ~ r2_hidden(X37,X38)
        | X37 = X39
        | r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_74,plain,(
    ! [X28] : k2_enumset1(X28,X28,X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_75,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_76,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_77,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) = k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_72]),c_0_48])).

cnf(c_0_79,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( k3_zfmisc_1(esk7_0,esk8_0,esk9_0) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_69])).

cnf(c_0_85,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) = X1
    | esk9_0 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) != k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_78])).

fof(c_0_86,plain,(
    ! [X40] : k9_relat_1(k1_xboole_0,X40) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

fof(c_0_87,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | k9_relat_1(X43,k3_xboole_0(X41,k10_relat_1(X43,X42))) = k3_xboole_0(k9_relat_1(X43,X41),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t150_funct_1])])).

fof(c_0_88,plain,(
    ! [X44] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X44)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

cnf(c_0_89,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k4_enumset1(X2,X2,X2,X2,X2,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_83])).

fof(c_0_90,plain,(
    ! [X18] : k5_xboole_0(X18,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_91,negated_conjecture,
    ( esk3_0 != esk7_0
    | esk4_0 != esk8_0
    | esk5_0 != esk9_0
    | esk6_0 != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_92,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk9_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_78])).

cnf(c_0_93,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),X1) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_84]),c_0_53])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),k2_zfmisc_1(X1,X2))
    | ~ r1_xboole_0(esk9_0,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_78])).

cnf(c_0_95,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k2_zfmisc_1(esk3_0,esk4_0)
    | k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_96,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_58])).

cnf(c_0_97,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_98,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,k10_relat_1(X1,X3))) = k3_xboole_0(k9_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_99,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_100,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1)))) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_103,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | esk7_0 != esk3_0
    | esk8_0 != esk4_0
    | esk9_0 != esk5_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_55])).

cnf(c_0_104,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk9_0 = esk5_0
    | esk9_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_105,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_93]),c_0_48])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))
    | ~ r1_xboole_0(esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_78])).

cnf(c_0_107,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk7_0 = X1
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_95]),c_0_96])).

cnf(c_0_108,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_97]),c_0_99]),c_0_100])])).

cnf(c_0_109,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_28]),c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( esk7_0 != esk3_0
    | esk8_0 != esk4_0
    | esk9_0 != esk5_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_103]),c_0_58]),c_0_48])).

cnf(c_0_111,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk9_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_104]),c_0_53]),c_0_105])).

cnf(c_0_112,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk8_0 = X1
    | k2_zfmisc_1(esk3_0,esk4_0) != k2_zfmisc_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_95]),c_0_96])).

cnf(c_0_113,negated_conjecture,
    ( ~ r1_xboole_0(esk9_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_106]),c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_107])).

cnf(c_0_115,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_108]),c_0_109])).

cnf(c_0_116,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk7_0 != esk3_0
    | esk8_0 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_117,negated_conjecture,
    ( esk8_0 = esk4_0
    | esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_112])).

cnf(c_0_118,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk7_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])])).

cnf(c_0_119,negated_conjecture,
    ( esk7_0 != esk3_0
    | esk8_0 != esk4_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_116]),c_0_58]),c_0_105])).

cnf(c_0_120,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_117]),c_0_115])])).

cnf(c_0_121,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_118]),c_0_58]),c_0_53]),c_0_105])).

cnf(c_0_122,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121])).

cnf(c_0_123,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_122]),c_0_58]),c_0_53]),c_0_105])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_123]),c_0_53]),c_0_53]),c_0_105]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.027 s
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.44  fof(t1_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.20/0.44  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.20/0.44  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.44  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.20/0.44  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.20/0.44  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.20/0.44  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.20/0.44  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.44  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 0.20/0.44  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.44  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.44  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.44  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 0.20/0.44  fof(t150_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_funct_1)).
% 0.20/0.44  fof(t45_ordinal1, axiom, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.20/0.44  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.44  fof(c_0_17, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.44  fof(c_0_18, plain, ![X49]:((r2_hidden(esk2_1(X49),X49)|X49=k1_xboole_0)&(r1_xboole_0(esk2_1(X49),X49)|X49=k1_xboole_0)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).
% 0.20/0.44  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.20/0.44  cnf(c_0_20, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.44  cnf(c_0_21, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.44  fof(c_0_22, plain, ![X9]:k3_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.44  fof(c_0_23, negated_conjecture, (k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0)=k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0)&(k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0)!=k1_xboole_0&(esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0|esk6_0!=esk10_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.44  fof(c_0_24, plain, ![X45, X46, X47, X48]:k4_zfmisc_1(X45,X46,X47,X48)=k2_zfmisc_1(k3_zfmisc_1(X45,X46,X47),X48), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.20/0.44  fof(c_0_25, plain, ![X51, X52, X53, X54]:k4_zfmisc_1(X51,X52,X53,X54)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X51,X52),X53),X54), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.20/0.44  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.44  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.44  cnf(c_0_28, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.44  cnf(c_0_29, negated_conjecture, (k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0)=k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_30, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.44  cnf(c_0_31, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.44  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 0.20/0.44  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X1),X1)|r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.44  cnf(c_0_34, negated_conjecture, (k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  fof(c_0_35, plain, ![X33, X34, X35, X36]:((X33=X35|(X33=k1_xboole_0|X34=k1_xboole_0)|k2_zfmisc_1(X33,X34)!=k2_zfmisc_1(X35,X36))&(X34=X36|(X33=k1_xboole_0|X34=k1_xboole_0)|k2_zfmisc_1(X33,X34)!=k2_zfmisc_1(X35,X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(k3_zfmisc_1(esk7_0,esk8_0,esk9_0),esk10_0)=k2_zfmisc_1(k3_zfmisc_1(esk3_0,esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30])).
% 0.20/0.44  cnf(c_0_37, plain, (k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.20/0.44  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_20, c_0_28])).
% 0.20/0.44  fof(c_0_39, plain, ![X29, X30, X31, X32]:((~r1_xboole_0(X29,X30)|r1_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X32)))&(~r1_xboole_0(X31,X32)|r1_xboole_0(k2_zfmisc_1(X29,X31),k2_zfmisc_1(X30,X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.20/0.44  cnf(c_0_40, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.44  cnf(c_0_41, plain, (r1_xboole_0(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(k3_zfmisc_1(esk3_0,esk4_0,esk5_0),esk6_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_34, c_0_30])).
% 0.20/0.44  cnf(c_0_43, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.44  cnf(c_0_44, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 0.20/0.44  cnf(c_0_45, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_21])).
% 0.20/0.44  cnf(c_0_46, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.44  cnf(c_0_47, plain, (X1=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.44  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_37])).
% 0.20/0.44  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)=k1_xboole_0|esk10_0=k1_xboole_0|esk10_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.44  cnf(c_0_50, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.44  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_47]), c_0_48])).
% 0.20/0.44  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)=k1_xboole_0|esk10_0=esk6_0|esk10_0=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.44  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.44  cnf(c_0_54, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.44  cnf(c_0_55, negated_conjecture, (esk10_0=k1_xboole_0|esk10_0=esk6_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_52]), c_0_53]), c_0_48])).
% 0.20/0.44  cnf(c_0_56, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_45, c_0_54])).
% 0.20/0.44  cnf(c_0_57, negated_conjecture, (esk10_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(ef,[status(thm)],[c_0_55])).
% 0.20/0.44  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 0.20/0.44  cnf(c_0_59, negated_conjecture, (X1=esk10_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X2,X1)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.44  cnf(c_0_60, negated_conjecture, (esk6_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_57]), c_0_58]), c_0_48])).
% 0.20/0.44  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)=k1_xboole_0|esk10_0=esk6_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_60])).
% 0.20/0.44  cnf(c_0_62, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.44  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk6_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.20/0.44  cnf(c_0_64, negated_conjecture, (esk10_0=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_61]), c_0_53])])).
% 0.20/0.44  cnf(c_0_65, plain, (k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)=X4|X5=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X5)!=k2_zfmisc_1(X4,X6)), inference(spm,[status(thm)],[c_0_62, c_0_37])).
% 0.20/0.44  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk6_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_60])).
% 0.20/0.44  cnf(c_0_67, negated_conjecture, (k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k1_xboole_0|k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)!=k2_zfmisc_1(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_60])).
% 0.20/0.44  cnf(c_0_68, negated_conjecture, (k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)|k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_66])).
% 0.20/0.44  cnf(c_0_69, negated_conjecture, (k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)|k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_67])).
% 0.20/0.44  cnf(c_0_70, negated_conjecture, (k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_68])).
% 0.20/0.44  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)=k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)|k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_70])).
% 0.20/0.44  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)=k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_71]), c_0_53])).
% 0.20/0.44  fof(c_0_73, plain, ![X37, X38, X39]:(((r2_hidden(X37,X38)|~r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))))&(X37!=X39|~r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39)))))&(~r2_hidden(X37,X38)|X37=X39|r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.44  fof(c_0_74, plain, ![X28]:k2_enumset1(X28,X28,X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.20/0.44  fof(c_0_75, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.44  fof(c_0_76, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.44  fof(c_0_77, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.44  cnf(c_0_78, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)=k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_72]), c_0_48])).
% 0.20/0.44  cnf(c_0_79, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.44  cnf(c_0_80, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.44  cnf(c_0_81, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.44  cnf(c_0_82, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.44  cnf(c_0_83, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.44  cnf(c_0_84, negated_conjecture, (k3_zfmisc_1(esk7_0,esk8_0,esk9_0)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_69])).
% 0.20/0.44  cnf(c_0_85, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)=X1|esk9_0=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)!=k2_zfmisc_1(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_78])).
% 0.20/0.44  fof(c_0_86, plain, ![X40]:k9_relat_1(k1_xboole_0,X40)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.20/0.44  fof(c_0_87, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|~v1_funct_1(X43)|k9_relat_1(X43,k3_xboole_0(X41,k10_relat_1(X43,X42)))=k3_xboole_0(k9_relat_1(X43,X41),X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t150_funct_1])])).
% 0.20/0.44  fof(c_0_88, plain, ![X44]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X44))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), inference(variable_rename,[status(thm)],[t45_ordinal1])).
% 0.20/0.44  cnf(c_0_89, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,k4_enumset1(X2,X2,X2,X2,X2,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82]), c_0_83])).
% 0.20/0.44  fof(c_0_90, plain, ![X18]:k5_xboole_0(X18,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.44  cnf(c_0_91, negated_conjecture, (esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0|esk6_0!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_92, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk9_0=k1_xboole_0|esk9_0=X1|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_78])).
% 0.20/0.44  cnf(c_0_93, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_84]), c_0_53])).
% 0.20/0.44  cnf(c_0_94, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),k2_zfmisc_1(X1,X2))|~r1_xboole_0(esk9_0,X2)), inference(spm,[status(thm)],[c_0_54, c_0_78])).
% 0.20/0.44  cnf(c_0_95, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k2_zfmisc_1(esk3_0,esk4_0)|k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk9_0=k1_xboole_0), inference(er,[status(thm)],[c_0_85])).
% 0.20/0.44  cnf(c_0_96, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_58])).
% 0.20/0.44  cnf(c_0_97, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.44  cnf(c_0_98, plain, (k9_relat_1(X1,k3_xboole_0(X2,k10_relat_1(X1,X3)))=k3_xboole_0(k9_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.44  cnf(c_0_99, plain, (v1_funct_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.44  cnf(c_0_100, plain, (v1_relat_1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.44  cnf(c_0_101, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1))))), inference(er,[status(thm)],[c_0_89])).
% 0.20/0.44  cnf(c_0_102, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.44  cnf(c_0_103, negated_conjecture, (esk10_0=k1_xboole_0|esk7_0!=esk3_0|esk8_0!=esk4_0|esk9_0!=esk5_0), inference(spm,[status(thm)],[c_0_91, c_0_55])).
% 0.20/0.44  cnf(c_0_104, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk9_0=esk5_0|esk9_0=k1_xboole_0), inference(er,[status(thm)],[c_0_92])).
% 0.20/0.44  cnf(c_0_105, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_93]), c_0_48])).
% 0.20/0.44  cnf(c_0_106, negated_conjecture, (r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0))|~r1_xboole_0(esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_94, c_0_78])).
% 0.20/0.44  cnf(c_0_107, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk7_0=X1|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_95]), c_0_96])).
% 0.20/0.44  cnf(c_0_108, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_97]), c_0_99]), c_0_100])])).
% 0.20/0.44  cnf(c_0_109, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_28]), c_0_102])).
% 0.20/0.44  cnf(c_0_110, negated_conjecture, (esk7_0!=esk3_0|esk8_0!=esk4_0|esk9_0!=esk5_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_103]), c_0_58]), c_0_48])).
% 0.20/0.44  cnf(c_0_111, negated_conjecture, (esk9_0=k1_xboole_0|esk9_0=esk5_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_104]), c_0_53]), c_0_105])).
% 0.20/0.44  cnf(c_0_112, negated_conjecture, (esk9_0=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk8_0=X1|k2_zfmisc_1(esk3_0,esk4_0)!=k2_zfmisc_1(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_95]), c_0_96])).
% 0.20/0.44  cnf(c_0_113, negated_conjecture, (~r1_xboole_0(esk9_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_106]), c_0_105])).
% 0.20/0.44  cnf(c_0_114, negated_conjecture, (esk7_0=esk3_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(er,[status(thm)],[c_0_107])).
% 0.20/0.44  cnf(c_0_115, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_108]), c_0_109])).
% 0.20/0.44  cnf(c_0_116, negated_conjecture, (esk9_0=k1_xboole_0|esk7_0!=esk3_0|esk8_0!=esk4_0), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.20/0.44  cnf(c_0_117, negated_conjecture, (esk8_0=esk4_0|esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(er,[status(thm)],[c_0_112])).
% 0.20/0.44  cnf(c_0_118, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|esk7_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])])).
% 0.20/0.44  cnf(c_0_119, negated_conjecture, (esk7_0!=esk3_0|esk8_0!=esk4_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_116]), c_0_58]), c_0_105])).
% 0.20/0.44  cnf(c_0_120, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0|esk8_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_117]), c_0_115])])).
% 0.20/0.44  cnf(c_0_121, negated_conjecture, (esk7_0=esk3_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_118]), c_0_58]), c_0_53]), c_0_105])).
% 0.20/0.44  cnf(c_0_122, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121])).
% 0.20/0.44  cnf(c_0_123, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_122]), c_0_58]), c_0_53]), c_0_105])).
% 0.20/0.44  cnf(c_0_124, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_123]), c_0_53]), c_0_53]), c_0_105]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 125
% 0.20/0.44  # Proof object clause steps            : 90
% 0.20/0.44  # Proof object formula steps           : 35
% 0.20/0.44  # Proof object conjectures             : 56
% 0.20/0.44  # Proof object clause conjectures      : 53
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 24
% 0.20/0.44  # Proof object initial formulas used   : 17
% 0.20/0.44  # Proof object generating inferences   : 57
% 0.20/0.44  # Proof object simplifying inferences  : 58
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 17
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 28
% 0.20/0.44  # Removed in clause preprocessing      : 5
% 0.20/0.44  # Initial clauses in saturation        : 23
% 0.20/0.44  # Processed clauses                    : 593
% 0.20/0.44  # ...of these trivial                  : 6
% 0.20/0.44  # ...subsumed                          : 317
% 0.20/0.44  # ...remaining for further processing  : 270
% 0.20/0.44  # Other redundant clauses eliminated   : 4
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 28
% 0.20/0.44  # Backward-rewritten                   : 50
% 0.20/0.44  # Generated clauses                    : 5083
% 0.20/0.44  # ...of the previous two non-trivial   : 2668
% 0.20/0.44  # Contextual simplify-reflections      : 5
% 0.20/0.44  # Paramodulations                      : 5041
% 0.20/0.44  # Factorizations                       : 21
% 0.20/0.44  # Equation resolutions                 : 21
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 191
% 0.20/0.44  #    Positive orientable unit clauses  : 17
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 11
% 0.20/0.44  #    Non-unit-clauses                  : 163
% 0.20/0.44  # Current number of unprocessed clauses: 1828
% 0.20/0.44  # ...number of literals in the above   : 5240
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 83
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 8974
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 8195
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 248
% 0.20/0.44  # Unit Clause-clause subsumption calls : 287
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 15
% 0.20/0.44  # BW rewrite match successes           : 12
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 56933
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.089 s
% 0.20/0.44  # System time              : 0.007 s
% 0.20/0.44  # Total time               : 0.096 s
% 0.20/0.44  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
