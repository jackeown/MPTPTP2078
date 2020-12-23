%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:16 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 347 expanded)
%              Number of clauses        :   47 ( 144 expanded)
%              Number of leaves         :   19 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  206 ( 870 expanded)
%              Number of equality atoms :   57 ( 272 expanded)
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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ r2_hidden(X20,X19)
      | r2_hidden(X20,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

fof(c_0_31,plain,(
    ! [X40,X42,X43,X44,X45,X46] :
      ( ( r2_hidden(esk1_1(X40),X40)
        | X40 = k1_xboole_0 )
      & ( ~ r2_hidden(X42,X43)
        | ~ r2_hidden(X43,X44)
        | ~ r2_hidden(X44,X45)
        | ~ r2_hidden(X45,X46)
        | ~ r2_hidden(X46,esk1_1(X40))
        | r1_xboole_0(X42,X40)
        | X40 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

fof(c_0_32,plain,(
    ! [X37,X38,X39] :
      ( ( k1_mcart_1(X37) = X38
        | ~ r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)) )
      & ( r2_hidden(k2_mcart_1(X37),X39)
        | ~ r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_33,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(k1_mcart_1(X34),X35)
        | ~ r2_hidden(X34,k2_zfmisc_1(X35,X36)) )
      & ( r2_hidden(k2_mcart_1(X34),X36)
        | ~ r2_hidden(X34,k2_zfmisc_1(X35,X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X47,X48)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ r2_hidden(X49,X47)
      | X48 = k1_xboole_0
      | r2_hidden(k1_funct_1(X50,X49),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk4_0),k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_26]),c_0_27]),c_0_28])).

fof(c_0_42,plain,(
    ! [X26,X27,X28] :
      ( ( X28 != k1_funct_1(X26,X27)
        | r2_hidden(k4_tarski(X27,X28),X26)
        | ~ r2_hidden(X27,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X28 = k1_funct_1(X26,X27)
        | ~ r2_hidden(X27,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X28 != k1_funct_1(X26,X27)
        | X28 = k1_xboole_0
        | r2_hidden(X27,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X28 != k1_xboole_0
        | X28 = k1_funct_1(X26,X27)
        | r2_hidden(X27,k1_relat_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_43,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk1_1(esk4_0)),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k1_mcart_1(esk1_1(esk4_0)) = esk2_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

fof(c_0_49,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_50,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_52,plain,(
    ! [X21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_53,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(X25)
      | v1_funct_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk2_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_63,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_65,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_67,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_70,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(k1_tarski(X16),X17) != k1_xboole_0
        | r2_hidden(X16,X17) )
      & ( ~ r2_hidden(X16,X17)
        | k4_xboole_0(k1_tarski(X16),X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(k1_xboole_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_64])).

cnf(c_0_72,plain,
    ( k1_funct_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),c_0_69])])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_74,plain,(
    ! [X9] : k4_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k1_funct_1(k1_xboole_0,X1),esk3_0)
    | ~ r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_72]),c_0_76])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k1_xboole_0)
    | k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_35])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_82]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.28  % Computer   : n005.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % WCLimit    : 600
% 0.09/0.28  % DateTime   : Tue Dec  1 20:13:17 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.28  # Version: 2.5pre002
% 0.09/0.28  # No SInE strategy applied
% 0.09/0.28  # Trying AutoSched0 for 299 seconds
% 0.14/0.32  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.14/0.32  # and selection function SelectNewComplexAHPNS.
% 0.14/0.32  #
% 0.14/0.32  # Preprocessing time       : 0.030 s
% 0.14/0.32  # Presaturation interreduction done
% 0.14/0.32  
% 0.14/0.32  # Proof found!
% 0.14/0.32  # SZS status Theorem
% 0.14/0.32  # SZS output start CNFRefutation
% 0.14/0.32  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 0.14/0.32  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.32  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.32  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.32  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.14/0.32  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.14/0.32  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.14/0.32  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.14/0.32  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.14/0.32  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.14/0.32  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.32  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.32  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.32  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.14/0.32  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.32  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.32  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.32  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.14/0.32  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.32  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.14/0.32  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.14/0.32  fof(c_0_21, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.32  fof(c_0_22, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.32  fof(c_0_23, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.32  fof(c_0_24, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~r2_hidden(X20,X19)|r2_hidden(X20,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.14/0.32  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.32  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.32  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.32  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.32  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.14/0.32  fof(c_0_31, plain, ![X40, X42, X43, X44, X45, X46]:((r2_hidden(esk1_1(X40),X40)|X40=k1_xboole_0)&(~r2_hidden(X42,X43)|~r2_hidden(X43,X44)|~r2_hidden(X44,X45)|~r2_hidden(X45,X46)|~r2_hidden(X46,esk1_1(X40))|r1_xboole_0(X42,X40)|X40=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.14/0.32  fof(c_0_32, plain, ![X37, X38, X39]:((k1_mcart_1(X37)=X38|~r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)))&(r2_hidden(k2_mcart_1(X37),X39)|~r2_hidden(X37,k2_zfmisc_1(k1_tarski(X38),X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.14/0.32  fof(c_0_33, plain, ![X34, X35, X36]:((r2_hidden(k1_mcart_1(X34),X35)|~r2_hidden(X34,k2_zfmisc_1(X35,X36)))&(r2_hidden(k2_mcart_1(X34),X36)|~r2_hidden(X34,k2_zfmisc_1(X35,X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.14/0.32  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.32  cnf(c_0_35, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.32  cnf(c_0_36, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.32  fof(c_0_37, plain, ![X47, X48, X49, X50]:(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|(~r2_hidden(X49,X47)|(X48=k1_xboole_0|r2_hidden(k1_funct_1(X50,X49),X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.14/0.32  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_39, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.32  cnf(c_0_40, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_1(esk4_0),k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.32  cnf(c_0_41, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_26]), c_0_27]), c_0_28])).
% 0.14/0.32  fof(c_0_42, plain, ![X26, X27, X28]:(((X28!=k1_funct_1(X26,X27)|r2_hidden(k4_tarski(X27,X28),X26)|~r2_hidden(X27,k1_relat_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(~r2_hidden(k4_tarski(X27,X28),X26)|X28=k1_funct_1(X26,X27)|~r2_hidden(X27,k1_relat_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26))))&((X28!=k1_funct_1(X26,X27)|X28=k1_xboole_0|r2_hidden(X27,k1_relat_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(X28!=k1_xboole_0|X28=k1_funct_1(X26,X27)|r2_hidden(X27,k1_relat_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.14/0.32  cnf(c_0_43, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.32  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_26]), c_0_27]), c_0_28])).
% 0.14/0.32  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_46, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_47, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(k1_mcart_1(esk1_1(esk4_0)),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.32  cnf(c_0_48, negated_conjecture, (k1_mcart_1(esk1_1(esk4_0))=esk2_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.14/0.32  fof(c_0_49, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.32  cnf(c_0_50, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.32  fof(c_0_51, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.32  fof(c_0_52, plain, ![X21]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.32  fof(c_0_53, plain, ![X25]:(~v1_xboole_0(X25)|v1_funct_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.14/0.32  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)|~r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_44]), c_0_45])]), c_0_46])).
% 0.14/0.32  cnf(c_0_55, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk2_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.32  cnf(c_0_56, negated_conjecture, (~r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_57, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.32  cnf(c_0_58, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(er,[status(thm)],[c_0_50])).
% 0.14/0.32  cnf(c_0_59, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.32  cnf(c_0_60, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.32  cnf(c_0_61, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.32  cnf(c_0_62, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.32  fof(c_0_63, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.32  cnf(c_0_64, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.14/0.32  cnf(c_0_65, plain, (k1_funct_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.14/0.32  cnf(c_0_66, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.32  cnf(c_0_67, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.14/0.32  cnf(c_0_68, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.14/0.32  cnf(c_0_69, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.14/0.32  fof(c_0_70, plain, ![X16, X17]:((k4_xboole_0(k1_tarski(X16),X17)!=k1_xboole_0|r2_hidden(X16,X17))&(~r2_hidden(X16,X17)|k4_xboole_0(k1_tarski(X16),X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.14/0.32  cnf(c_0_71, negated_conjecture, (~r2_hidden(k1_funct_1(k1_xboole_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_56, c_0_64])).
% 0.14/0.32  cnf(c_0_72, plain, (k1_funct_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), c_0_69])])).
% 0.14/0.32  cnf(c_0_73, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.14/0.32  fof(c_0_74, plain, ![X9]:k4_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.32  cnf(c_0_75, negated_conjecture, (r2_hidden(k1_funct_1(k1_xboole_0,X1),esk3_0)|~r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(rw,[status(thm)],[c_0_54, c_0_64])).
% 0.14/0.32  cnf(c_0_76, negated_conjecture, (~r2_hidden(k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.14/0.32  cnf(c_0_77, plain, (r2_hidden(X1,X2)|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_26]), c_0_27]), c_0_28])).
% 0.14/0.32  cnf(c_0_78, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.14/0.32  cnf(c_0_79, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_72]), c_0_76])).
% 0.14/0.32  cnf(c_0_80, plain, (r2_hidden(X1,k1_xboole_0)|k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.14/0.32  cnf(c_0_81, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_35])).
% 0.14/0.32  cnf(c_0_82, negated_conjecture, (r2_hidden(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.14/0.32  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_82]), c_0_69])]), ['proof']).
% 0.14/0.32  # SZS output end CNFRefutation
% 0.14/0.32  # Proof object total steps             : 84
% 0.14/0.32  # Proof object clause steps            : 47
% 0.14/0.32  # Proof object formula steps           : 37
% 0.14/0.32  # Proof object conjectures             : 24
% 0.14/0.32  # Proof object clause conjectures      : 21
% 0.14/0.32  # Proof object formula conjectures     : 3
% 0.14/0.32  # Proof object initial clauses used    : 23
% 0.14/0.32  # Proof object initial formulas used   : 19
% 0.14/0.32  # Proof object generating inferences   : 15
% 0.14/0.32  # Proof object simplifying inferences  : 29
% 0.14/0.32  # Training examples: 0 positive, 0 negative
% 0.14/0.32  # Parsed axioms                        : 20
% 0.14/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.32  # Initial clauses                      : 32
% 0.14/0.32  # Removed in clause preprocessing      : 3
% 0.14/0.32  # Initial clauses in saturation        : 29
% 0.14/0.32  # Processed clauses                    : 106
% 0.14/0.32  # ...of these trivial                  : 0
% 0.14/0.32  # ...subsumed                          : 9
% 0.14/0.32  # ...remaining for further processing  : 97
% 0.14/0.32  # Other redundant clauses eliminated   : 3
% 0.14/0.32  # Clauses deleted for lack of memory   : 0
% 0.14/0.32  # Backward-subsumed                    : 1
% 0.14/0.32  # Backward-rewritten                   : 25
% 0.14/0.32  # Generated clauses                    : 135
% 0.14/0.32  # ...of the previous two non-trivial   : 139
% 0.14/0.32  # Contextual simplify-reflections      : 0
% 0.14/0.32  # Paramodulations                      : 132
% 0.14/0.32  # Factorizations                       : 0
% 0.14/0.32  # Equation resolutions                 : 3
% 0.14/0.32  # Propositional unsat checks           : 0
% 0.14/0.32  #    Propositional check models        : 0
% 0.14/0.32  #    Propositional check unsatisfiable : 0
% 0.14/0.32  #    Propositional clauses             : 0
% 0.14/0.32  #    Propositional clauses after purity: 0
% 0.14/0.32  #    Propositional unsat core size     : 0
% 0.14/0.32  #    Propositional preprocessing time  : 0.000
% 0.14/0.32  #    Propositional encoding time       : 0.000
% 0.14/0.32  #    Propositional solver time         : 0.000
% 0.14/0.32  #    Success case prop preproc time    : 0.000
% 0.14/0.32  #    Success case prop encoding time   : 0.000
% 0.14/0.32  #    Success case prop solver time     : 0.000
% 0.14/0.32  # Current number of processed clauses  : 41
% 0.14/0.32  #    Positive orientable unit clauses  : 14
% 0.14/0.32  #    Positive unorientable unit clauses: 0
% 0.14/0.32  #    Negative unit clauses             : 2
% 0.14/0.32  #    Non-unit-clauses                  : 25
% 0.14/0.32  # Current number of unprocessed clauses: 87
% 0.14/0.32  # ...number of literals in the above   : 251
% 0.14/0.32  # Current number of archived formulas  : 0
% 0.14/0.32  # Current number of archived clauses   : 56
% 0.14/0.32  # Clause-clause subsumption calls (NU) : 322
% 0.14/0.32  # Rec. Clause-clause subsumption calls : 154
% 0.14/0.32  # Non-unit clause-clause subsumptions  : 9
% 0.14/0.32  # Unit Clause-clause subsumption calls : 50
% 0.14/0.32  # Rewrite failures with RHS unbound    : 0
% 0.14/0.32  # BW rewrite match attempts            : 7
% 0.14/0.32  # BW rewrite match successes           : 7
% 0.14/0.32  # Condensation attempts                : 0
% 0.14/0.32  # Condensation successes               : 0
% 0.14/0.32  # Termbank termtop insertions          : 4282
% 0.14/0.32  
% 0.14/0.32  # -------------------------------------------------
% 0.14/0.32  # User time                : 0.035 s
% 0.14/0.32  # System time              : 0.004 s
% 0.14/0.32  # Total time               : 0.039 s
% 0.14/0.32  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
