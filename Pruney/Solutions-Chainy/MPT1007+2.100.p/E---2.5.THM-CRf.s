%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 498 expanded)
%              Number of clauses        :   59 ( 208 expanded)
%              Number of leaves         :   20 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  255 (1310 expanded)
%              Number of equality atoms :   65 ( 447 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))
    & esk7_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | r1_tarski(X33,X31)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r1_tarski(X34,X31)
        | r2_hidden(X34,X32)
        | X32 != k1_zfmisc_1(X31) )
      & ( ~ r2_hidden(esk3_2(X35,X36),X36)
        | ~ r1_tarski(esk3_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) )
      & ( r2_hidden(esk3_2(X35,X36),X36)
        | r1_tarski(esk3_2(X35,X36),X35)
        | X36 = k1_zfmisc_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_27,plain,(
    ! [X47,X48] :
      ( ~ m1_subset_1(X47,X48)
      | v1_xboole_0(X48)
      | r2_hidden(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X46] : ~ v1_xboole_0(k1_zfmisc_1(X46)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_34,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_35,plain,(
    ! [X56,X58,X59,X60,X61,X62] :
      ( ( r2_hidden(esk5_1(X56),X56)
        | X56 = k1_xboole_0 )
      & ( ~ r2_hidden(X58,X59)
        | ~ r2_hidden(X59,X60)
        | ~ r2_hidden(X60,X61)
        | ~ r2_hidden(X61,X62)
        | ~ r2_hidden(X62,esk5_1(X56))
        | r1_xboole_0(X58,X56)
        | X56 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

fof(c_0_36,plain,(
    ! [X14] : k3_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X42,X43,X44,X45] :
      ( ( ~ r1_xboole_0(X42,X43)
        | r1_xboole_0(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X45)) )
      & ( ~ r1_xboole_0(X44,X45)
        | r1_xboole_0(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

fof(c_0_45,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_50,plain,(
    ! [X40,X41] :
      ( r2_hidden(X40,X41)
      | r1_xboole_0(k1_tarski(X40),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_51,plain,
    ( ~ r1_xboole_0(X1,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_43])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_48])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X1)
    | r2_hidden(esk2_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_43])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( ~ r1_xboole_0(X1,X1)
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_60,plain,(
    ! [X49] :
      ( ( k1_relat_1(X49) != k1_xboole_0
        | X49 = k1_xboole_0
        | ~ v1_relat_1(X49) )
      & ( k2_relat_1(X49) != k1_xboole_0
        | X49 = k1_xboole_0
        | ~ v1_relat_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_61,plain,(
    ! [X53,X55] :
      ( v1_relat_1(esk4_1(X53))
      & v1_funct_1(esk4_1(X53))
      & k1_relat_1(esk4_1(X53)) = X53
      & ( ~ r2_hidden(X55,X53)
        | k1_funct_1(esk4_1(X53),X55) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_29]),c_0_30]),c_0_31]),c_0_32])).

fof(c_0_64,plain,(
    ! [X63,X64,X65,X66] :
      ( ~ v1_funct_1(X66)
      | ~ v1_funct_2(X66,X63,X64)
      | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
      | ~ r2_hidden(X65,X63)
      | X64 = k1_xboole_0
      | r2_hidden(k1_funct_1(X66,X65),X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_67,plain,(
    ! [X50,X51,X52] :
      ( ( X52 != k1_funct_1(X50,X51)
        | r2_hidden(k4_tarski(X51,X52),X50)
        | ~ r2_hidden(X51,k1_relat_1(X50))
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( ~ r2_hidden(k4_tarski(X51,X52),X50)
        | X52 = k1_funct_1(X50,X51)
        | ~ r2_hidden(X51,k1_relat_1(X50))
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( X52 != k1_funct_1(X50,X51)
        | X52 = k1_xboole_0
        | r2_hidden(X51,k1_relat_1(X50))
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( X52 != k1_xboole_0
        | X52 = k1_funct_1(X50,X51)
        | r2_hidden(X51,k1_relat_1(X50))
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k1_relat_1(esk4_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( v1_relat_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk8_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_76,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk6_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_78,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( esk4_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])])).

cnf(c_0_80,plain,
    ( v1_funct_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_39]),c_0_74]),c_0_75])]),c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk6_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_42])).

cnf(c_0_84,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_79])).

cnf(c_0_86,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_79])).

cnf(c_0_87,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_71])).

cnf(c_0_90,plain,
    ( k1_funct_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87])]),c_0_88])).

fof(c_0_91,plain,(
    ! [X38,X39] : ~ v1_xboole_0(k2_tarski(X38,X39)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_89]),c_0_90])).

cnf(c_0_93,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_89]),c_0_90]),c_0_92])).

cnf(c_0_95,plain,
    ( ~ v1_xboole_0(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_96,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_42])).

cnf(c_0_97,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.40  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.40  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.20/0.40  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.40  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.20/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.40  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.20/0.40  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.40  fof(s3_funct_1__e9_44_1__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 0.20/0.40  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.20/0.40  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.20/0.40  fof(fc3_xboole_0, axiom, ![X1, X2]:~(v1_xboole_0(k2_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 0.20/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.40  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.20/0.40  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))))&(esk7_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.40  fof(c_0_22, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_23, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_24, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_25, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  fof(c_0_26, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|r1_tarski(X33,X31)|X32!=k1_zfmisc_1(X31))&(~r1_tarski(X34,X31)|r2_hidden(X34,X32)|X32!=k1_zfmisc_1(X31)))&((~r2_hidden(esk3_2(X35,X36),X36)|~r1_tarski(esk3_2(X35,X36),X35)|X36=k1_zfmisc_1(X35))&(r2_hidden(esk3_2(X35,X36),X36)|r1_tarski(esk3_2(X35,X36),X35)|X36=k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.40  fof(c_0_27, plain, ![X47, X48]:(~m1_subset_1(X47,X48)|(v1_xboole_0(X48)|r2_hidden(X47,X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  fof(c_0_33, plain, ![X46]:~v1_xboole_0(k1_zfmisc_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.40  fof(c_0_34, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.40  fof(c_0_35, plain, ![X56, X58, X59, X60, X61, X62]:((r2_hidden(esk5_1(X56),X56)|X56=k1_xboole_0)&(~r2_hidden(X58,X59)|~r2_hidden(X59,X60)|~r2_hidden(X60,X61)|~r2_hidden(X61,X62)|~r2_hidden(X62,esk5_1(X56))|r1_xboole_0(X58,X56)|X56=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.20/0.40  fof(c_0_36, plain, ![X14]:k3_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.40  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_38, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.40  cnf(c_0_40, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.40  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_42, plain, (r2_hidden(esk5_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_43, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.40  fof(c_0_44, plain, ![X42, X43, X44, X45]:((~r1_xboole_0(X42,X43)|r1_xboole_0(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X45)))&(~r1_xboole_0(X44,X45)|r1_xboole_0(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.20/0.40  fof(c_0_45, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.40  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (r2_hidden(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.20/0.40  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.40  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  fof(c_0_50, plain, ![X40, X41]:(r2_hidden(X40,X41)|r1_xboole_0(k1_tarski(X40),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.20/0.40  cnf(c_0_51, plain, (~r1_xboole_0(X1,X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_43])).
% 0.20/0.40  cnf(c_0_52, plain, (r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.40  cnf(c_0_53, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.40  cnf(c_0_55, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_48])).
% 0.20/0.40  cnf(c_0_56, plain, (r1_xboole_0(X1,X1)|r2_hidden(esk2_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_49, c_0_43])).
% 0.20/0.40  cnf(c_0_57, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_58, plain, (~r1_xboole_0(X1,X1)|~r2_hidden(X2,k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.40  fof(c_0_60, plain, ![X49]:((k1_relat_1(X49)!=k1_xboole_0|X49=k1_xboole_0|~v1_relat_1(X49))&(k2_relat_1(X49)!=k1_xboole_0|X49=k1_xboole_0|~v1_relat_1(X49))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.40  fof(c_0_61, plain, ![X53, X55]:(((v1_relat_1(esk4_1(X53))&v1_funct_1(esk4_1(X53)))&k1_relat_1(esk4_1(X53))=X53)&(~r2_hidden(X55,X53)|k1_funct_1(esk4_1(X53),X55)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e9_44_1__funct_1])])])])).
% 0.20/0.40  cnf(c_0_62, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.40  cnf(c_0_63, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.40  fof(c_0_64, plain, ![X63, X64, X65, X66]:(~v1_funct_1(X66)|~v1_funct_2(X66,X63,X64)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))|(~r2_hidden(X65,X63)|(X64=k1_xboole_0|r2_hidden(k1_funct_1(X66,X65),X64)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (~r1_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.40  fof(c_0_67, plain, ![X50, X51, X52]:(((X52!=k1_funct_1(X50,X51)|r2_hidden(k4_tarski(X51,X52),X50)|~r2_hidden(X51,k1_relat_1(X50))|(~v1_relat_1(X50)|~v1_funct_1(X50)))&(~r2_hidden(k4_tarski(X51,X52),X50)|X52=k1_funct_1(X50,X51)|~r2_hidden(X51,k1_relat_1(X50))|(~v1_relat_1(X50)|~v1_funct_1(X50))))&((X52!=k1_funct_1(X50,X51)|X52=k1_xboole_0|r2_hidden(X51,k1_relat_1(X50))|(~v1_relat_1(X50)|~v1_funct_1(X50)))&(X52!=k1_xboole_0|X52=k1_funct_1(X50,X51)|r2_hidden(X51,k1_relat_1(X50))|(~v1_relat_1(X50)|~v1_funct_1(X50))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.20/0.40  cnf(c_0_68, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.40  cnf(c_0_69, plain, (k1_relat_1(esk4_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.40  cnf(c_0_70, plain, (v1_relat_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_72, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.40  cnf(c_0_73, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk8_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (r2_hidden(esk6_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_66, c_0_63])).
% 0.20/0.40  cnf(c_0_78, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.40  cnf(c_0_79, plain, (esk4_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])])).
% 0.20/0.40  cnf(c_0_80, plain, (v1_funct_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)|~r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_39]), c_0_74]), c_0_75])]), c_0_76])).
% 0.20/0.40  cnf(c_0_83, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk6_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_77, c_0_42])).
% 0.20/0.40  cnf(c_0_84, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_78])).
% 0.20/0.40  cnf(c_0_85, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_79])).
% 0.20/0.40  cnf(c_0_86, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_79])).
% 0.20/0.40  cnf(c_0_87, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_79])).
% 0.20/0.40  cnf(c_0_88, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_81])).
% 0.20/0.40  cnf(c_0_89, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_71])).
% 0.20/0.40  cnf(c_0_90, plain, (k1_funct_1(k1_xboole_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_87])]), c_0_88])).
% 0.20/0.40  fof(c_0_91, plain, ![X38, X39]:~v1_xboole_0(k2_tarski(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).
% 0.20/0.40  cnf(c_0_92, negated_conjecture, (~r2_hidden(k1_xboole_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_89]), c_0_90])).
% 0.20/0.40  cnf(c_0_93, plain, (~v1_xboole_0(k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.40  cnf(c_0_94, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_89]), c_0_90]), c_0_92])).
% 0.20/0.40  cnf(c_0_95, plain, (~v1_xboole_0(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.40  cnf(c_0_96, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_42])).
% 0.20/0.40  cnf(c_0_97, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.40  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 99
% 0.20/0.40  # Proof object clause steps            : 59
% 0.20/0.40  # Proof object formula steps           : 40
% 0.20/0.40  # Proof object conjectures             : 24
% 0.20/0.40  # Proof object clause conjectures      : 21
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 27
% 0.20/0.40  # Proof object initial formulas used   : 20
% 0.20/0.40  # Proof object generating inferences   : 24
% 0.20/0.40  # Proof object simplifying inferences  : 37
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 20
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 39
% 0.20/0.40  # Removed in clause preprocessing      : 4
% 0.20/0.40  # Initial clauses in saturation        : 35
% 0.20/0.40  # Processed clauses                    : 228
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 50
% 0.20/0.40  # ...remaining for further processing  : 178
% 0.20/0.40  # Other redundant clauses eliminated   : 6
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 7
% 0.20/0.40  # Backward-rewritten                   : 30
% 0.20/0.40  # Generated clauses                    : 1602
% 0.20/0.40  # ...of the previous two non-trivial   : 1021
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 1596
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 6
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 136
% 0.20/0.40  #    Positive orientable unit clauses  : 18
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 5
% 0.20/0.40  #    Non-unit-clauses                  : 113
% 0.20/0.40  # Current number of unprocessed clauses: 816
% 0.20/0.40  # ...number of literals in the above   : 2157
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 41
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 3211
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 2743
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 38
% 0.20/0.40  # Unit Clause-clause subsumption calls : 77
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 8
% 0.20/0.40  # BW rewrite match successes           : 7
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 20509
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.052 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
