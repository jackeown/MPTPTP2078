%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:15 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 360 expanded)
%              Number of clauses        :   40 ( 145 expanded)
%              Number of leaves         :   14 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  192 ( 974 expanded)
%              Number of equality atoms :   42 ( 295 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ( X34 != k1_funct_1(X32,X33)
        | r2_hidden(k4_tarski(X33,X34),X32)
        | ~ r2_hidden(X33,k1_relat_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(k4_tarski(X33,X34),X32)
        | X34 = k1_funct_1(X32,X33)
        | ~ r2_hidden(X33,k1_relat_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X34 != k1_funct_1(X32,X33)
        | X34 = k1_xboole_0
        | r2_hidden(X33,k1_relat_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X34 != k1_xboole_0
        | X34 = k1_funct_1(X32,X33)
        | r2_hidden(X33,k1_relat_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))
    & esk5_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ v5_relat_1(X36,X35)
      | ~ v1_funct_1(X36)
      | ~ r2_hidden(X37,k1_relat_1(X36))
      | r2_hidden(k1_funct_1(X36,X37),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_21,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X43,X44,X45] :
      ( ( v4_relat_1(X45,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( v5_relat_1(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | v1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_28,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ r2_hidden(X21,X20)
      | r2_hidden(X21,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,X46,X47)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | ~ r2_hidden(X48,X46)
      | X47 = k1_xboole_0
      | r2_hidden(k1_funct_1(X49,X48),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_38,plain,(
    ! [X17] : m1_subset_1(esk1_1(X17),X17) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_39,plain,(
    ! [X12] : ~ v1_xboole_0(k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_40,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X13 = X15
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)) )
      & ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)) )
      & ( X13 != X15
        | ~ r2_hidden(X14,X16)
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_47,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_55,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,k1_funct_1(X1,X2)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),esk5_0)
    | ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_48]),c_0_45])]),c_0_49])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk6_0,X1)),k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_45]),c_0_46])])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk6_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk1_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_xboole_0
    | X1 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( esk1_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_67]),c_0_63]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.35  % Computer   : n025.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 19:00:20 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.19/0.38  # and selection function SelectNewComplexAHPNS.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 0.19/0.38  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 0.19/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.38  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.19/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.38  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.19/0.38  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.19/0.38  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.19/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.19/0.38  fof(c_0_15, plain, ![X32, X33, X34]:(((X34!=k1_funct_1(X32,X33)|r2_hidden(k4_tarski(X33,X34),X32)|~r2_hidden(X33,k1_relat_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(~r2_hidden(k4_tarski(X33,X34),X32)|X34=k1_funct_1(X32,X33)|~r2_hidden(X33,k1_relat_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32))))&((X34!=k1_funct_1(X32,X33)|X34=k1_xboole_0|r2_hidden(X33,k1_relat_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(X34!=k1_xboole_0|X34=k1_funct_1(X32,X33)|r2_hidden(X33,k1_relat_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))))&(esk5_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk6_0,esk4_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.19/0.38  fof(c_0_17, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_18, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_19, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_20, plain, ![X35, X36, X37]:(~v1_relat_1(X36)|~v5_relat_1(X36,X35)|~v1_funct_1(X36)|(~r2_hidden(X37,k1_relat_1(X36))|r2_hidden(k1_funct_1(X36,X37),X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.19/0.38  cnf(c_0_21, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_22, plain, ![X43, X44, X45]:((v4_relat_1(X45,X43)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(v5_relat_1(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_27, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  fof(c_0_28, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|(~r2_hidden(X21,X20)|r2_hidden(X21,X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_30, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_31, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_32, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_34, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  fof(c_0_35, plain, ![X46, X47, X48, X49]:(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|(~r2_hidden(X48,X46)|(X47=k1_xboole_0|r2_hidden(k1_funct_1(X49,X48),X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_37, plain, ![X22, X23]:(~m1_subset_1(X22,X23)|(v1_xboole_0(X23)|r2_hidden(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.38  fof(c_0_38, plain, ![X17]:m1_subset_1(esk1_1(X17),X17), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.19/0.38  fof(c_0_39, plain, ![X12]:~v1_xboole_0(k1_tarski(X12)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.19/0.38  fof(c_0_40, plain, ![X13, X14, X15, X16]:(((X13=X15|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)))&(r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16))))&(X13!=X15|~r2_hidden(X14,X16)|r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(k1_tarski(X15),X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_41, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_42, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_43, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(k1_funct_1(X1,X2),X3)|~v5_relat_1(X1,X3)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.19/0.38  cnf(c_0_47, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_50, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_51, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_52, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_53, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 0.19/0.38  cnf(c_0_55, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,k1_funct_1(X1,X2)),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_31])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (~r2_hidden(k1_funct_1(esk6_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk6_0,X1)=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),esk5_0)|~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_48]), c_0_45])]), c_0_49])).
% 0.19/0.38  cnf(c_0_59, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.38  cnf(c_0_60, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_61, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk6_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,k1_funct_1(esk6_0,X1)),k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_45]), c_0_46])])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk6_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk1_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k1_funct_1(esk6_0,X1)=k1_xboole_0|X1=esk4_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (~r2_hidden(k1_xboole_0,esk5_0)), inference(rw,[status(thm)],[c_0_56, c_0_63])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (esk1_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_67]), c_0_63]), c_0_66]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 69
% 0.19/0.38  # Proof object clause steps            : 40
% 0.19/0.38  # Proof object formula steps           : 29
% 0.19/0.38  # Proof object conjectures             : 22
% 0.19/0.38  # Proof object clause conjectures      : 19
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 19
% 0.19/0.38  # Proof object initial formulas used   : 14
% 0.19/0.38  # Proof object generating inferences   : 13
% 0.19/0.38  # Proof object simplifying inferences  : 30
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 23
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 35
% 0.19/0.38  # Removed in clause preprocessing      : 3
% 0.19/0.38  # Initial clauses in saturation        : 32
% 0.19/0.38  # Processed clauses                    : 119
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 3
% 0.19/0.38  # ...remaining for further processing  : 116
% 0.19/0.38  # Other redundant clauses eliminated   : 4
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 4
% 0.19/0.38  # Generated clauses                    : 119
% 0.19/0.38  # ...of the previous two non-trivial   : 112
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 115
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 4
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 76
% 0.19/0.39  #    Positive orientable unit clauses  : 23
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 50
% 0.19/0.39  # Current number of unprocessed clauses: 55
% 0.19/0.39  # ...number of literals in the above   : 188
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 39
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 383
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 155
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.39  # Unit Clause-clause subsumption calls : 49
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 4
% 0.19/0.39  # BW rewrite match successes           : 3
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 4637
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.033 s
% 0.19/0.39  # System time              : 0.006 s
% 0.19/0.39  # Total time               : 0.038 s
% 0.19/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
