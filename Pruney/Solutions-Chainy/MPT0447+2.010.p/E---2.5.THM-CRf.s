%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:23 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 231 expanded)
%              Number of clauses        :   55 ( 106 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  252 ( 599 expanded)
%              Number of equality atoms :   35 (  85 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(c_0_22,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk2_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk2_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_23,plain,(
    ! [X31] : r1_xboole_0(X31,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_24,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,k2_xboole_0(X26,X27))
      | r1_tarski(k4_xboole_0(X25,X26),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_25,plain,(
    ! [X44,X45] : k3_tarski(k2_tarski(X44,X45)) = k2_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X46,X47,X49] :
      ( ( r2_hidden(esk4_2(X46,X47),X47)
        | ~ r2_hidden(X46,X47) )
      & ( ~ r2_hidden(X49,X47)
        | ~ r2_hidden(X49,esk4_2(X46,X47))
        | ~ r2_hidden(X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X35,X36] : k2_tarski(X35,X36) = k2_tarski(X36,X35) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_33,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(k4_xboole_0(X28,X29),X30)
      | r1_tarski(X28,k2_xboole_0(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_34,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_35,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_tarski(esk8_0,esk9_0)
    & ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(esk4_2(X1,k1_xboole_0),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_45,plain,(
    ! [X56,X57,X58,X60,X61,X62,X63,X65] :
      ( ( ~ r2_hidden(X58,X57)
        | r2_hidden(k4_tarski(X58,esk5_3(X56,X57,X58)),X56)
        | X57 != k1_relat_1(X56) )
      & ( ~ r2_hidden(k4_tarski(X60,X61),X56)
        | r2_hidden(X60,X57)
        | X57 != k1_relat_1(X56) )
      & ( ~ r2_hidden(esk6_2(X62,X63),X63)
        | ~ r2_hidden(k4_tarski(esk6_2(X62,X63),X65),X62)
        | X63 = k1_relat_1(X62) )
      & ( r2_hidden(esk6_2(X62,X63),X63)
        | r2_hidden(k4_tarski(esk6_2(X62,X63),esk7_2(X62,X63)),X62)
        | X63 = k1_relat_1(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_46,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | r1_tarski(X16,k2_xboole_0(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_47,plain,(
    ! [X67] :
      ( ~ v1_relat_1(X67)
      | k3_relat_1(X67) = k2_xboole_0(k1_relat_1(X67),k2_relat_1(X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_48,plain,(
    ! [X68,X69] :
      ( ~ v1_relat_1(X68)
      | ~ v1_relat_1(X69)
      | r1_tarski(k6_subset_1(k1_relat_1(X68),k1_relat_1(X69)),k1_relat_1(k6_subset_1(X68,X69))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_49,plain,(
    ! [X50,X51] : k6_subset_1(X50,X51) = k4_xboole_0(X50,X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_50,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_51,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,esk5_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_58,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_59,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(X32,X33)
      | ~ r1_tarski(X34,X33)
      | r1_tarski(k2_xboole_0(X32,X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_62,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | v1_relat_1(X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_63,plain,(
    ! [X52,X53] :
      ( ( ~ m1_subset_1(X52,k1_zfmisc_1(X53))
        | r1_tarski(X52,X53) )
      & ( ~ r1_tarski(X52,X53)
        | m1_subset_1(X52,k1_zfmisc_1(X53)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_64,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_65,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk8_0,X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_70,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_31])).

cnf(c_0_74,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_31])).

fof(c_0_75,plain,(
    ! [X70,X71] :
      ( ( r1_tarski(k1_relat_1(X70),k1_relat_1(X71))
        | ~ r1_tarski(X70,X71)
        | ~ v1_relat_1(X71)
        | ~ v1_relat_1(X70) )
      & ( r1_tarski(k2_relat_1(X70),k2_relat_1(X71))
        | ~ r1_tarski(X70,X71)
        | ~ v1_relat_1(X71)
        | ~ v1_relat_1(X70) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_76,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_78,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk8_0,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_71])).

cnf(c_0_83,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_31])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(esk8_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_89,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_92,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_74])).

cnf(c_0_93,plain,
    ( r1_tarski(k2_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_74])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk8_0),k1_relat_1(esk9_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_90]),c_0_91]),c_0_89]),c_0_67])])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_97,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_90]),c_0_67])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_90]),c_0_98]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:29:42 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 1.37/1.57  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.37/1.57  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.37/1.57  #
% 1.37/1.57  # Preprocessing time       : 0.029 s
% 1.37/1.57  
% 1.37/1.57  # Proof found!
% 1.37/1.57  # SZS status Theorem
% 1.37/1.57  # SZS output start CNFRefutation
% 1.37/1.57  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.37/1.57  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.37/1.57  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.37/1.57  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.37/1.57  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.37/1.57  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 1.37/1.57  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.37/1.57  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.37/1.57  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.37/1.57  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.37/1.57  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.37/1.57  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.37/1.57  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.37/1.57  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 1.37/1.57  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.37/1.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.37/1.57  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.37/1.57  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 1.37/1.57  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.37/1.57  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.37/1.57  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.37/1.57  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.37/1.57  fof(c_0_22, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk2_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk2_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.37/1.57  fof(c_0_23, plain, ![X31]:r1_xboole_0(X31,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 1.37/1.57  fof(c_0_24, plain, ![X25, X26, X27]:(~r1_tarski(X25,k2_xboole_0(X26,X27))|r1_tarski(k4_xboole_0(X25,X26),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.37/1.57  fof(c_0_25, plain, ![X44, X45]:k3_tarski(k2_tarski(X44,X45))=k2_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.37/1.57  fof(c_0_26, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 1.37/1.57  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.37/1.57  cnf(c_0_28, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.37/1.57  fof(c_0_29, plain, ![X46, X47, X49]:((r2_hidden(esk4_2(X46,X47),X47)|~r2_hidden(X46,X47))&(~r2_hidden(X49,X47)|~r2_hidden(X49,esk4_2(X46,X47))|~r2_hidden(X46,X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 1.37/1.57  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.37/1.57  cnf(c_0_31, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.37/1.57  fof(c_0_32, plain, ![X35, X36]:k2_tarski(X35,X36)=k2_tarski(X36,X35), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.37/1.57  fof(c_0_33, plain, ![X28, X29, X30]:(~r1_tarski(k4_xboole_0(X28,X29),X30)|r1_tarski(X28,k2_xboole_0(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.37/1.57  fof(c_0_34, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X20,X21)|r1_tarski(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.37/1.57  fof(c_0_35, negated_conjecture, (v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&(r1_tarski(esk8_0,esk9_0)&~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 1.37/1.57  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.37/1.57  cnf(c_0_37, plain, (r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.37/1.57  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 1.37/1.57  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.37/1.57  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.37/1.57  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.37/1.57  cnf(c_0_42, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.37/1.57  fof(c_0_43, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.37/1.57  cnf(c_0_44, plain, (~r2_hidden(esk4_2(X1,k1_xboole_0),X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.37/1.57  fof(c_0_45, plain, ![X56, X57, X58, X60, X61, X62, X63, X65]:(((~r2_hidden(X58,X57)|r2_hidden(k4_tarski(X58,esk5_3(X56,X57,X58)),X56)|X57!=k1_relat_1(X56))&(~r2_hidden(k4_tarski(X60,X61),X56)|r2_hidden(X60,X57)|X57!=k1_relat_1(X56)))&((~r2_hidden(esk6_2(X62,X63),X63)|~r2_hidden(k4_tarski(esk6_2(X62,X63),X65),X62)|X63=k1_relat_1(X62))&(r2_hidden(esk6_2(X62,X63),X63)|r2_hidden(k4_tarski(esk6_2(X62,X63),esk7_2(X62,X63)),X62)|X63=k1_relat_1(X62)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.37/1.57  fof(c_0_46, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|r1_tarski(X16,k2_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 1.37/1.57  fof(c_0_47, plain, ![X67]:(~v1_relat_1(X67)|k3_relat_1(X67)=k2_xboole_0(k1_relat_1(X67),k2_relat_1(X67))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.37/1.57  fof(c_0_48, plain, ![X68, X69]:(~v1_relat_1(X68)|(~v1_relat_1(X69)|r1_tarski(k6_subset_1(k1_relat_1(X68),k1_relat_1(X69)),k1_relat_1(k6_subset_1(X68,X69))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 1.37/1.57  fof(c_0_49, plain, ![X50, X51]:k6_subset_1(X50,X51)=k4_xboole_0(X50,X51), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.37/1.57  fof(c_0_50, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.37/1.57  fof(c_0_51, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.37/1.57  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.37/1.57  cnf(c_0_53, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_40, c_0_31])).
% 1.37/1.57  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,esk9_0)|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.37/1.57  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.37/1.57  cnf(c_0_56, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_37])).
% 1.37/1.57  cnf(c_0_57, plain, (r2_hidden(k4_tarski(X1,esk5_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.37/1.57  fof(c_0_58, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 1.37/1.57  fof(c_0_59, plain, ![X32, X33, X34]:(~r1_tarski(X32,X33)|~r1_tarski(X34,X33)|r1_tarski(k2_xboole_0(X32,X34),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.37/1.57  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.37/1.57  cnf(c_0_61, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.37/1.57  fof(c_0_62, plain, ![X54, X55]:(~v1_relat_1(X54)|(~m1_subset_1(X55,k1_zfmisc_1(X54))|v1_relat_1(X55))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.37/1.57  fof(c_0_63, plain, ![X52, X53]:((~m1_subset_1(X52,k1_zfmisc_1(X53))|r1_tarski(X52,X53))&(~r1_tarski(X52,X53)|m1_subset_1(X52,k1_zfmisc_1(X53)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.37/1.57  cnf(c_0_64, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.37/1.57  cnf(c_0_65, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.37/1.57  cnf(c_0_66, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.37/1.57  cnf(c_0_67, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.37/1.57  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.37/1.57  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(esk8_0,X1),esk9_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.37/1.57  cnf(c_0_70, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.37/1.57  cnf(c_0_71, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.37/1.57  cnf(c_0_72, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.37/1.57  cnf(c_0_73, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_60, c_0_31])).
% 1.37/1.57  cnf(c_0_74, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_61, c_0_31])).
% 1.37/1.57  fof(c_0_75, plain, ![X70, X71]:((r1_tarski(k1_relat_1(X70),k1_relat_1(X71))|~r1_tarski(X70,X71)|~v1_relat_1(X71)|~v1_relat_1(X70))&(r1_tarski(k2_relat_1(X70),k2_relat_1(X71))|~r1_tarski(X70,X71)|~v1_relat_1(X71)|~v1_relat_1(X70))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 1.37/1.57  cnf(c_0_76, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.37/1.57  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.37/1.57  cnf(c_0_78, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65])).
% 1.37/1.57  cnf(c_0_79, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.37/1.57  cnf(c_0_80, negated_conjecture, (r1_tarski(k4_xboole_0(esk8_0,esk9_0),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.37/1.57  cnf(c_0_81, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_70])).
% 1.37/1.57  cnf(c_0_82, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_56, c_0_71])).
% 1.37/1.57  cnf(c_0_83, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_31])).
% 1.37/1.57  cnf(c_0_84, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 1.37/1.57  cnf(c_0_85, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.37/1.57  cnf(c_0_86, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.37/1.57  cnf(c_0_87, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_66, c_0_78])).
% 1.37/1.57  cnf(c_0_88, negated_conjecture, (k4_xboole_0(esk8_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 1.37/1.57  cnf(c_0_89, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.37/1.57  cnf(c_0_90, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.37/1.57  cnf(c_0_91, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.37/1.57  cnf(c_0_92, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_83, c_0_74])).
% 1.37/1.57  cnf(c_0_93, plain, (r1_tarski(k2_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 1.37/1.57  cnf(c_0_94, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_53, c_0_74])).
% 1.37/1.57  cnf(c_0_95, negated_conjecture, (k4_xboole_0(k1_relat_1(esk8_0),k1_relat_1(esk9_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_90]), c_0_91]), c_0_89]), c_0_67])])).
% 1.37/1.57  cnf(c_0_96, negated_conjecture, (~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.37/1.57  cnf(c_0_97, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_86])).
% 1.37/1.57  cnf(c_0_98, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_90]), c_0_67])])).
% 1.37/1.57  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_90]), c_0_98]), c_0_42])]), ['proof']).
% 1.37/1.57  # SZS output end CNFRefutation
% 1.37/1.57  # Proof object total steps             : 100
% 1.37/1.57  # Proof object clause steps            : 55
% 1.37/1.57  # Proof object formula steps           : 45
% 1.37/1.57  # Proof object conjectures             : 14
% 1.37/1.57  # Proof object clause conjectures      : 11
% 1.37/1.57  # Proof object formula conjectures     : 3
% 1.37/1.57  # Proof object initial clauses used    : 25
% 1.37/1.57  # Proof object initial formulas used   : 22
% 1.37/1.57  # Proof object generating inferences   : 24
% 1.37/1.57  # Proof object simplifying inferences  : 22
% 1.37/1.57  # Training examples: 0 positive, 0 negative
% 1.37/1.57  # Parsed axioms                        : 23
% 1.37/1.57  # Removed by relevancy pruning/SinE    : 0
% 1.37/1.57  # Initial clauses                      : 40
% 1.37/1.57  # Removed in clause preprocessing      : 2
% 1.37/1.57  # Initial clauses in saturation        : 38
% 1.37/1.57  # Processed clauses                    : 4007
% 1.37/1.57  # ...of these trivial                  : 46
% 1.37/1.57  # ...subsumed                          : 2592
% 1.37/1.57  # ...remaining for further processing  : 1369
% 1.37/1.57  # Other redundant clauses eliminated   : 8
% 1.37/1.57  # Clauses deleted for lack of memory   : 0
% 1.37/1.57  # Backward-subsumed                    : 89
% 1.37/1.57  # Backward-rewritten                   : 36
% 1.37/1.57  # Generated clauses                    : 69821
% 1.37/1.57  # ...of the previous two non-trivial   : 62055
% 1.37/1.57  # Contextual simplify-reflections      : 95
% 1.37/1.57  # Paramodulations                      : 69731
% 1.37/1.57  # Factorizations                       : 11
% 1.37/1.57  # Equation resolutions                 : 78
% 1.37/1.57  # Propositional unsat checks           : 0
% 1.37/1.57  #    Propositional check models        : 0
% 1.37/1.57  #    Propositional check unsatisfiable : 0
% 1.37/1.57  #    Propositional clauses             : 0
% 1.37/1.57  #    Propositional clauses after purity: 0
% 1.37/1.57  #    Propositional unsat core size     : 0
% 1.37/1.57  #    Propositional preprocessing time  : 0.000
% 1.37/1.57  #    Propositional encoding time       : 0.000
% 1.37/1.57  #    Propositional solver time         : 0.000
% 1.37/1.57  #    Success case prop preproc time    : 0.000
% 1.37/1.57  #    Success case prop encoding time   : 0.000
% 1.37/1.57  #    Success case prop solver time     : 0.000
% 1.37/1.57  # Current number of processed clauses  : 1240
% 1.37/1.57  #    Positive orientable unit clauses  : 96
% 1.37/1.57  #    Positive unorientable unit clauses: 1
% 1.37/1.57  #    Negative unit clauses             : 10
% 1.37/1.57  #    Non-unit-clauses                  : 1133
% 1.37/1.57  # Current number of unprocessed clauses: 57812
% 1.37/1.57  # ...number of literals in the above   : 214084
% 1.37/1.57  # Current number of archived formulas  : 0
% 1.37/1.57  # Current number of archived clauses   : 128
% 1.37/1.57  # Clause-clause subsumption calls (NU) : 198599
% 1.37/1.57  # Rec. Clause-clause subsumption calls : 90703
% 1.37/1.57  # Non-unit clause-clause subsumptions  : 1898
% 1.37/1.57  # Unit Clause-clause subsumption calls : 4918
% 1.37/1.57  # Rewrite failures with RHS unbound    : 0
% 1.37/1.57  # BW rewrite match attempts            : 2596
% 1.37/1.57  # BW rewrite match successes           : 14
% 1.37/1.57  # Condensation attempts                : 0
% 1.37/1.57  # Condensation successes               : 0
% 1.37/1.57  # Termbank termtop insertions          : 1120383
% 1.37/1.57  
% 1.37/1.57  # -------------------------------------------------
% 1.37/1.57  # User time                : 1.174 s
% 1.37/1.57  # System time              : 0.047 s
% 1.37/1.57  # Total time               : 1.221 s
% 1.37/1.57  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
