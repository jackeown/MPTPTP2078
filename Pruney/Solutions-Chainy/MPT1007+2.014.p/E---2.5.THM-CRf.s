%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:16 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 337 expanded)
%              Number of clauses        :   48 ( 140 expanded)
%              Number of leaves         :   20 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 ( 838 expanded)
%              Number of equality atoms :   46 ( 253 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))
    & esk4_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ r2_hidden(X21,X20)
      | r2_hidden(X21,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

fof(c_0_32,plain,(
    ! [X43,X45,X46,X47,X48,X49] :
      ( ( r2_hidden(esk2_1(X43),X43)
        | X43 = k1_xboole_0 )
      & ( ~ r2_hidden(X45,X46)
        | ~ r2_hidden(X46,X47)
        | ~ r2_hidden(X47,X48)
        | ~ r2_hidden(X48,X49)
        | ~ r2_hidden(X49,esk2_1(X43))
        | r1_xboole_0(X45,X43)
        | X43 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

fof(c_0_33,plain,(
    ! [X40,X41,X42] :
      ( ( k1_mcart_1(X40) = X41
        | ~ r2_hidden(X40,k2_zfmisc_1(k1_tarski(X41),X42)) )
      & ( r2_hidden(k2_mcart_1(X40),X42)
        | ~ r2_hidden(X40,k2_zfmisc_1(k1_tarski(X41),X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_34,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(k1_mcart_1(X37),X38)
        | ~ r2_hidden(X37,k2_zfmisc_1(X38,X39)) )
      & ( r2_hidden(k2_mcart_1(X37),X39)
        | ~ r2_hidden(X37,k2_zfmisc_1(X38,X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X50,X51,X52,X53] :
      ( ~ v1_funct_1(X53)
      | ~ v1_funct_2(X53,X50,X51)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | ~ r2_hidden(X52,X50)
      | X51 = k1_xboole_0
      | r2_hidden(k1_funct_1(X53,X52),X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_40,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_41,plain,(
    ! [X17] : m1_subset_1(esk1_1(X17),X17) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_42,plain,(
    ! [X15,X16] : ~ v1_xboole_0(k2_tarski(X15,X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_43,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_1(esk5_0),k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_46,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk2_1(esk5_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( k1_mcart_1(esk2_1(esk5_0)) = esk3_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

fof(c_0_55,plain,(
    ! [X29,X30,X31] :
      ( ( X31 != k1_funct_1(X29,X30)
        | r2_hidden(k4_tarski(X30,X31),X29)
        | ~ r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),X29)
        | X31 = k1_funct_1(X29,X30)
        | ~ r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X31 != k1_funct_1(X29,X30)
        | X31 = k1_xboole_0
        | r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X31 != k1_xboole_0
        | X31 = k1_funct_1(X29,X30)
        | r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_56,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | v1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_57,plain,(
    ! [X22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_58,plain,(
    ! [X28] :
      ( ~ v1_xboole_0(X28)
      | v1_funct_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),esk4_0)
    | ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_47]),c_0_48])]),c_0_49])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_28]),c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_64,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk1_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_62]),c_0_63])).

cnf(c_0_71,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_73,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_75,plain,(
    ! [X32,X33] :
      ( ~ r2_hidden(X32,X33)
      | ~ r1_tarski(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k1_funct_1(k1_xboole_0,esk1_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,plain,
    ( k1_funct_1(k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])])).

fof(c_0_78,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(k1_xboole_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_70])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k1_xboole_0)
    | r2_hidden(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_85]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:06:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.22/0.39  # and selection function SelectNewComplexAHPNS.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.028 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.22/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.22/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.22/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.22/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.22/0.39  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.22/0.39  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.22/0.39  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.22/0.39  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.22/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.22/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.22/0.39  fof(fc3_xboole_0, axiom, ![X1, X2]:~(v1_xboole_0(k2_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 0.22/0.39  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.22/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.22/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.22/0.39  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.22/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.22/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.22/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.22/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.22/0.39  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.22/0.39  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))&(esk4_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.22/0.39  fof(c_0_22, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.22/0.39  fof(c_0_23, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.22/0.39  fof(c_0_24, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.22/0.39  fof(c_0_25, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|(~r2_hidden(X21,X20)|r2_hidden(X21,X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.22/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.39  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.39  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.22/0.39  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.22/0.39  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.22/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.22/0.39  fof(c_0_32, plain, ![X43, X45, X46, X47, X48, X49]:((r2_hidden(esk2_1(X43),X43)|X43=k1_xboole_0)&(~r2_hidden(X45,X46)|~r2_hidden(X46,X47)|~r2_hidden(X47,X48)|~r2_hidden(X48,X49)|~r2_hidden(X49,esk2_1(X43))|r1_xboole_0(X45,X43)|X43=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.22/0.39  fof(c_0_33, plain, ![X40, X41, X42]:((k1_mcart_1(X40)=X41|~r2_hidden(X40,k2_zfmisc_1(k1_tarski(X41),X42)))&(r2_hidden(k2_mcart_1(X40),X42)|~r2_hidden(X40,k2_zfmisc_1(k1_tarski(X41),X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.22/0.39  fof(c_0_34, plain, ![X37, X38, X39]:((r2_hidden(k1_mcart_1(X37),X38)|~r2_hidden(X37,k2_zfmisc_1(X38,X39)))&(r2_hidden(k2_mcart_1(X37),X39)|~r2_hidden(X37,k2_zfmisc_1(X38,X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.22/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.22/0.39  cnf(c_0_36, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.22/0.39  cnf(c_0_37, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.22/0.39  fof(c_0_38, plain, ![X50, X51, X52, X53]:(~v1_funct_1(X53)|~v1_funct_2(X53,X50,X51)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|(~r2_hidden(X52,X50)|(X51=k1_xboole_0|r2_hidden(k1_funct_1(X53,X52),X51)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.22/0.39  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.39  fof(c_0_40, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.22/0.39  fof(c_0_41, plain, ![X17]:m1_subset_1(esk1_1(X17),X17), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.22/0.39  fof(c_0_42, plain, ![X15, X16]:~v1_xboole_0(k2_tarski(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).
% 0.22/0.39  cnf(c_0_43, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.22/0.39  cnf(c_0_44, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_1(esk5_0),k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.22/0.39  cnf(c_0_45, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_27]), c_0_28]), c_0_29])).
% 0.22/0.39  cnf(c_0_46, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.22/0.39  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_27]), c_0_28]), c_0_29])).
% 0.22/0.39  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.39  cnf(c_0_49, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.39  cnf(c_0_50, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.22/0.39  cnf(c_0_51, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.22/0.39  cnf(c_0_52, plain, (~v1_xboole_0(k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.22/0.39  cnf(c_0_53, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k1_mcart_1(esk2_1(esk5_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.22/0.39  cnf(c_0_54, negated_conjecture, (k1_mcart_1(esk2_1(esk5_0))=esk3_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.22/0.39  fof(c_0_55, plain, ![X29, X30, X31]:(((X31!=k1_funct_1(X29,X30)|r2_hidden(k4_tarski(X30,X31),X29)|~r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(~r2_hidden(k4_tarski(X30,X31),X29)|X31=k1_funct_1(X29,X30)|~r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29))))&((X31!=k1_funct_1(X29,X30)|X31=k1_xboole_0|r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X31!=k1_xboole_0|X31=k1_funct_1(X29,X30)|r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.22/0.39  fof(c_0_56, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.22/0.39  fof(c_0_57, plain, ![X22]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.22/0.39  fof(c_0_58, plain, ![X28]:(~v1_xboole_0(X28)|v1_funct_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.22/0.39  cnf(c_0_59, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),esk4_0)|~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_47]), c_0_48])]), c_0_49])).
% 0.22/0.39  cnf(c_0_60, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.22/0.39  cnf(c_0_61, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_28]), c_0_29])).
% 0.22/0.39  cnf(c_0_62, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk3_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.22/0.39  cnf(c_0_63, negated_conjecture, (~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.39  cnf(c_0_64, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.22/0.39  cnf(c_0_65, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.22/0.39  cnf(c_0_66, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.22/0.39  cnf(c_0_67, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.22/0.39  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.22/0.39  cnf(c_0_69, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk1_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.22/0.39  cnf(c_0_70, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_62]), c_0_63])).
% 0.22/0.39  cnf(c_0_71, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(er,[status(thm)],[c_0_64])).
% 0.22/0.39  cnf(c_0_72, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.22/0.39  cnf(c_0_73, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.22/0.39  cnf(c_0_74, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.22/0.39  fof(c_0_75, plain, ![X32, X33]:(~r2_hidden(X32,X33)|~r1_tarski(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.22/0.39  cnf(c_0_76, negated_conjecture, (r2_hidden(k1_funct_1(k1_xboole_0,esk1_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.22/0.39  cnf(c_0_77, plain, (k1_funct_1(k1_xboole_0,X1)=k1_xboole_0|r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])])).
% 0.22/0.39  fof(c_0_78, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.22/0.39  cnf(c_0_79, negated_conjecture, (~r2_hidden(k1_funct_1(k1_xboole_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_63, c_0_70])).
% 0.22/0.39  cnf(c_0_80, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.22/0.39  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k1_xboole_0)|r2_hidden(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.22/0.39  cnf(c_0_82, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.22/0.39  cnf(c_0_83, negated_conjecture, (r2_hidden(esk3_0,k1_xboole_0)|~r2_hidden(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_79, c_0_77])).
% 0.22/0.39  cnf(c_0_84, negated_conjecture, (r2_hidden(k1_xboole_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])])).
% 0.22/0.39  cnf(c_0_85, negated_conjecture, (r2_hidden(esk3_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 0.22/0.39  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_85]), c_0_82])]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 87
% 0.22/0.39  # Proof object clause steps            : 48
% 0.22/0.39  # Proof object formula steps           : 39
% 0.22/0.39  # Proof object conjectures             : 25
% 0.22/0.39  # Proof object clause conjectures      : 22
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 24
% 0.22/0.39  # Proof object initial formulas used   : 20
% 0.22/0.39  # Proof object generating inferences   : 16
% 0.22/0.39  # Proof object simplifying inferences  : 29
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 21
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 32
% 0.22/0.39  # Removed in clause preprocessing      : 3
% 0.22/0.39  # Initial clauses in saturation        : 29
% 0.22/0.39  # Processed clauses                    : 113
% 0.22/0.39  # ...of these trivial                  : 1
% 0.22/0.39  # ...subsumed                          : 10
% 0.22/0.39  # ...remaining for further processing  : 102
% 0.22/0.39  # Other redundant clauses eliminated   : 3
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 20
% 0.22/0.39  # Generated clauses                    : 154
% 0.22/0.39  # ...of the previous two non-trivial   : 157
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 151
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 3
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 52
% 0.22/0.39  #    Positive orientable unit clauses  : 14
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 4
% 0.22/0.39  #    Non-unit-clauses                  : 34
% 0.22/0.39  # Current number of unprocessed clauses: 98
% 0.22/0.39  # ...number of literals in the above   : 295
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 50
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 354
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 181
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.22/0.39  # Unit Clause-clause subsumption calls : 21
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 2
% 0.22/0.39  # BW rewrite match successes           : 2
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 4490
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.034 s
% 0.22/0.39  # System time              : 0.005 s
% 0.22/0.39  # Total time               : 0.039 s
% 0.22/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
