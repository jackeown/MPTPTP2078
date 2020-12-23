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
% DateTime   : Thu Dec  3 11:04:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 943 expanded)
%              Number of clauses        :   80 ( 392 expanded)
%              Number of leaves         :   25 ( 269 expanded)
%              Depth                    :   15
%              Number of atoms          :  312 (2003 expanded)
%              Number of equality atoms :   82 ( 586 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(fc11_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(c_0_25,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | ~ v1_xboole_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_26,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_28,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_30,plain,(
    ! [X63,X65,X66,X67,X68,X69] :
      ( ( r2_hidden(esk3_1(X63),X63)
        | X63 = k1_xboole_0 )
      & ( ~ r2_hidden(X65,X66)
        | ~ r2_hidden(X66,X67)
        | ~ r2_hidden(X67,X68)
        | ~ r2_hidden(X68,X69)
        | ~ r2_hidden(X69,esk3_1(X63))
        | r1_xboole_0(X65,X63)
        | X63 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X38,X39] :
      ( ( ~ v4_relat_1(X39,X38)
        | r1_tarski(k1_relat_1(X39),X38)
        | ~ v1_relat_1(X39) )
      & ( ~ r1_tarski(k1_relat_1(X39),X38)
        | v4_relat_1(X39,X38)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_34,plain,(
    ! [X56,X57,X58] :
      ( ( v4_relat_1(X58,X56)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v5_relat_1(X58,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,k1_tarski(esk4_0),esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))
    & esk5_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_38,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_40,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_41,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_42,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_43,plain,(
    ! [X40] :
      ( ~ v1_xboole_0(X40)
      | v1_xboole_0(k2_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).

cnf(c_0_44,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_49,plain,(
    ! [X35] :
      ( ~ v1_xboole_0(X35)
      | v1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_55,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | v1_relat_1(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_56,plain,(
    ! [X44,X45] : v1_relat_1(k2_zfmisc_1(X44,X45)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_57,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | r1_tarski(k9_relat_1(X47,X46),k2_relat_1(X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_42])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_61,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_63,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_65,plain,(
    ! [X41,X42,X43] :
      ( ( v1_relat_1(k7_relat_1(X43,X41))
        | ~ v1_relat_1(X43)
        | ~ v4_relat_1(X43,X42) )
      & ( v4_relat_1(k7_relat_1(X43,X41),X41)
        | ~ v1_relat_1(X43)
        | ~ v4_relat_1(X43,X42) )
      & ( v4_relat_1(k7_relat_1(X43,X41),X42)
        | ~ v1_relat_1(X43)
        | ~ v4_relat_1(X43,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_67,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_71,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | k2_relat_1(k7_relat_1(X49,X48)) = k9_relat_1(X49,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_72,plain,(
    ! [X53] :
      ( ~ v1_relat_1(X53)
      | k7_relat_1(X53,k1_relat_1(X53)) = X53 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_73,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_42])).

cnf(c_0_74,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_48])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_36])).

cnf(c_0_77,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( v4_relat_1(esk7_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_68])])).

cnf(c_0_80,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_81,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_63])).

cnf(c_0_82,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

fof(c_0_85,plain,(
    ! [X52] :
      ( ( k1_relat_1(X52) != k1_xboole_0
        | X52 = k1_xboole_0
        | ~ v1_relat_1(X52) )
      & ( k2_relat_1(X52) != k1_xboole_0
        | X52 = k1_xboole_0
        | ~ v1_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_86,plain,
    ( v4_relat_1(k2_zfmisc_1(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk7_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_79])])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_81]),c_0_48])])).

cnf(c_0_90,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_48])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_93,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_86]),c_0_68])])).

fof(c_0_94,plain,(
    ! [X59,X60,X61,X62] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | k7_relset_1(X59,X60,X61,X62) = k9_relat_1(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk7_0,X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_87]),c_0_88])])).

cnf(c_0_96,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_42])).

cnf(c_0_97,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_75])])).

cnf(c_0_98,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_68])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_100,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

fof(c_0_101,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X55)
      | ~ v1_funct_1(X55)
      | k1_relat_1(X55) != k1_tarski(X54)
      | k2_relat_1(X55) = k1_tarski(k1_funct_1(X55,X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

cnf(c_0_102,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_95]),c_0_88])])).

cnf(c_0_103,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_48])])).

cnf(c_0_104,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_98])).

fof(c_0_105,plain,(
    ! [X28,X29] :
      ( ( ~ r1_tarski(X28,k1_tarski(X29))
        | X28 = k1_xboole_0
        | X28 = k1_tarski(X29) )
      & ( X28 != k1_xboole_0
        | r1_tarski(X28,k1_tarski(X29)) )
      & ( X28 != k1_tarski(X29)
        | r1_tarski(X28,k1_tarski(X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk7_0,esk6_0),k3_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_107,negated_conjecture,
    ( k7_relset_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk7_0,X1) = k9_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_66])).

cnf(c_0_108,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( k9_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_102]),c_0_103]),c_0_79])])).

cnf(c_0_110,plain,
    ( v4_relat_1(X1,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_48])).

cnf(c_0_111,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_112,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk7_0,esk6_0),k3_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,plain,
    ( k2_relat_1(X1) = k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k3_enumset1(X2,X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_114,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_115,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_69])).

cnf(c_0_116,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_109]),c_0_79])])).

cnf(c_0_117,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_110]),c_0_48])])).

cnf(c_0_118,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_119,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != k1_relat_1(esk7_0)
    | ~ r1_tarski(k9_relat_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_79])])).

cnf(c_0_120,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_42])).

cnf(c_0_121,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_48]),c_0_79])])).

cnf(c_0_122,plain,
    ( k1_relat_1(X1) = k3_enumset1(X2,X2,X2,X2,X2)
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_45])).

cnf(c_0_123,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_69]),c_0_79])])).

cnf(c_0_124,negated_conjecture,
    ( k9_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_79]),c_0_48])])).

cnf(c_0_125,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ v1_xboole_0(k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_102]),c_0_79])])).

cnf(c_0_126,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_78]),c_0_79])]),c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_124]),c_0_62])])).

cnf(c_0_128,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126]),c_0_48])])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128]),c_0_62])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:51:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.40  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 0.20/0.40  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.20/0.40  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(fc11_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 0.20/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.40  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.20/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.40  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.20/0.40  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 0.20/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.40  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.40  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.20/0.40  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.20/0.40  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.40  fof(c_0_25, plain, ![X32, X33, X34]:(~r2_hidden(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(X34))|~v1_xboole_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.40  fof(c_0_26, plain, ![X30, X31]:((~m1_subset_1(X30,k1_zfmisc_1(X31))|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|m1_subset_1(X30,k1_zfmisc_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.40  fof(c_0_27, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  fof(c_0_28, plain, ![X12, X13, X14, X15, X16]:((~r1_tarski(X12,X13)|(~r2_hidden(X14,X12)|r2_hidden(X14,X13)))&((r2_hidden(esk2_2(X15,X16),X15)|r1_tarski(X15,X16))&(~r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.40  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.20/0.40  fof(c_0_30, plain, ![X63, X65, X66, X67, X68, X69]:((r2_hidden(esk3_1(X63),X63)|X63=k1_xboole_0)&(~r2_hidden(X65,X66)|~r2_hidden(X66,X67)|~r2_hidden(X67,X68)|~r2_hidden(X68,X69)|~r2_hidden(X69,esk3_1(X63))|r1_xboole_0(X65,X63)|X63=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.20/0.40  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  fof(c_0_33, plain, ![X38, X39]:((~v4_relat_1(X39,X38)|r1_tarski(k1_relat_1(X39),X38)|~v1_relat_1(X39))&(~r1_tarski(k1_relat_1(X39),X38)|v4_relat_1(X39,X38)|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.40  fof(c_0_34, plain, ![X56, X57, X58]:((v4_relat_1(X58,X56)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(v5_relat_1(X58,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.40  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_36, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  fof(c_0_37, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,k1_tarski(esk4_0),esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))))&(esk5_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.20/0.40  fof(c_0_38, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_39, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_40, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_41, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  cnf(c_0_42, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_43, plain, ![X40]:(~v1_xboole_0(X40)|v1_xboole_0(k2_relat_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).
% 0.20/0.40  cnf(c_0_44, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.40  cnf(c_0_45, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.40  cnf(c_0_46, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_48, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.40  fof(c_0_49, plain, ![X35]:(~v1_xboole_0(X35)|v1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_51, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_52, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  fof(c_0_55, plain, ![X36, X37]:(~v1_relat_1(X36)|(~m1_subset_1(X37,k1_zfmisc_1(X36))|v1_relat_1(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.40  fof(c_0_56, plain, ![X44, X45]:v1_relat_1(k2_zfmisc_1(X44,X45)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.40  fof(c_0_57, plain, ![X46, X47]:(~v1_relat_1(X47)|r1_tarski(k9_relat_1(X47,X46),k2_relat_1(X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.20/0.40  cnf(c_0_58, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_42])).
% 0.20/0.40  cnf(c_0_59, plain, (v1_xboole_0(k2_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_60, plain, (~v4_relat_1(X1,X2)|~v1_relat_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.40  cnf(c_0_61, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.20/0.40  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.40  cnf(c_0_63, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.40  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  fof(c_0_65, plain, ![X41, X42, X43]:(((v1_relat_1(k7_relat_1(X43,X41))|(~v1_relat_1(X43)|~v4_relat_1(X43,X42)))&(v4_relat_1(k7_relat_1(X43,X41),X41)|(~v1_relat_1(X43)|~v4_relat_1(X43,X42))))&(v4_relat_1(k7_relat_1(X43,X41),X42)|(~v1_relat_1(X43)|~v4_relat_1(X43,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_54])).
% 0.20/0.40  cnf(c_0_67, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.40  cnf(c_0_68, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.40  cnf(c_0_69, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.40  cnf(c_0_70, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.40  fof(c_0_71, plain, ![X48, X49]:(~v1_relat_1(X49)|k2_relat_1(k7_relat_1(X49,X48))=k9_relat_1(X49,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.40  fof(c_0_72, plain, ![X53]:(~v1_relat_1(X53)|k7_relat_1(X53,k1_relat_1(X53))=X53), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.40  cnf(c_0_73, plain, (k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_60, c_0_42])).
% 0.20/0.40  cnf(c_0_74, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.40  cnf(c_0_75, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_48])).
% 0.20/0.40  cnf(c_0_76, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_64, c_0_36])).
% 0.20/0.40  cnf(c_0_77, plain, (v4_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (v4_relat_1(esk7_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_66])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_66]), c_0_68])])).
% 0.20/0.40  cnf(c_0_80, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.40  cnf(c_0_81, plain, (r1_tarski(k9_relat_1(X1,X2),k1_xboole_0)|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_63])).
% 0.20/0.40  cnf(c_0_82, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.40  cnf(c_0_83, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.40  cnf(c_0_84, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.20/0.40  fof(c_0_85, plain, ![X52]:((k1_relat_1(X52)!=k1_xboole_0|X52=k1_xboole_0|~v1_relat_1(X52))&(k2_relat_1(X52)!=k1_xboole_0|X52=k1_xboole_0|~v1_relat_1(X52))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.40  cnf(c_0_86, plain, (v4_relat_1(k2_zfmisc_1(X1,X2),X1)), inference(spm,[status(thm)],[c_0_61, c_0_76])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, (v4_relat_1(k7_relat_1(esk7_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.20/0.40  cnf(c_0_88, negated_conjecture, (v1_relat_1(k7_relat_1(esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_78]), c_0_79])])).
% 0.20/0.40  cnf(c_0_89, plain, (~r2_hidden(X1,k9_relat_1(X2,X3))|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_81]), c_0_48])])).
% 0.20/0.40  cnf(c_0_90, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.40  cnf(c_0_91, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_48])).
% 0.20/0.40  cnf(c_0_92, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.40  cnf(c_0_93, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_86]), c_0_68])])).
% 0.20/0.40  fof(c_0_94, plain, ![X59, X60, X61, X62]:(~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|k7_relset_1(X59,X60,X61,X62)=k9_relat_1(X61,X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.20/0.40  cnf(c_0_95, negated_conjecture, (k1_relat_1(k7_relat_1(esk7_0,X1))=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_87]), c_0_88])])).
% 0.20/0.40  cnf(c_0_96, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_89, c_0_42])).
% 0.20/0.40  cnf(c_0_97, plain, (k9_relat_1(k1_xboole_0,k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_75])])).
% 0.20/0.40  cnf(c_0_98, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_68])])).
% 0.20/0.40  cnf(c_0_99, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk4_0),esk5_0,esk7_0,esk6_0),k1_tarski(k1_funct_1(esk7_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_100, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.20/0.40  fof(c_0_101, plain, ![X54, X55]:(~v1_relat_1(X55)|~v1_funct_1(X55)|(k1_relat_1(X55)!=k1_tarski(X54)|k2_relat_1(X55)=k1_tarski(k1_funct_1(X55,X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.20/0.40  cnf(c_0_102, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_95]), c_0_88])])).
% 0.20/0.40  cnf(c_0_103, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_48])])).
% 0.20/0.40  cnf(c_0_104, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_61, c_0_98])).
% 0.20/0.40  fof(c_0_105, plain, ![X28, X29]:((~r1_tarski(X28,k1_tarski(X29))|(X28=k1_xboole_0|X28=k1_tarski(X29)))&((X28!=k1_xboole_0|r1_tarski(X28,k1_tarski(X29)))&(X28!=k1_tarski(X29)|r1_tarski(X28,k1_tarski(X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.40  cnf(c_0_106, negated_conjecture, (~r1_tarski(k7_relset_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk7_0,esk6_0),k3_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54])).
% 0.20/0.40  cnf(c_0_107, negated_conjecture, (k7_relset_1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk7_0,X1)=k9_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_100, c_0_66])).
% 0.20/0.40  cnf(c_0_108, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.20/0.40  cnf(c_0_109, negated_conjecture, (k9_relat_1(esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_102]), c_0_103]), c_0_79])])).
% 0.20/0.40  cnf(c_0_110, plain, (v4_relat_1(X1,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_104, c_0_48])).
% 0.20/0.40  cnf(c_0_111, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.20/0.40  cnf(c_0_112, negated_conjecture, (~r1_tarski(k9_relat_1(esk7_0,esk6_0),k3_enumset1(k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0),k1_funct_1(esk7_0,esk4_0)))), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 0.20/0.40  cnf(c_0_113, plain, (k2_relat_1(X1)=k3_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k3_enumset1(X2,X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54])).
% 0.20/0.40  cnf(c_0_114, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_115, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_69])).
% 0.20/0.40  cnf(c_0_116, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|~v1_xboole_0(k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_109]), c_0_79])])).
% 0.20/0.40  cnf(c_0_117, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_110]), c_0_48])])).
% 0.20/0.40  cnf(c_0_118, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54])).
% 0.20/0.40  cnf(c_0_119, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=k1_relat_1(esk7_0)|~r1_tarski(k9_relat_1(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114]), c_0_79])])).
% 0.20/0.40  cnf(c_0_120, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_115, c_0_42])).
% 0.20/0.40  cnf(c_0_121, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|~r1_tarski(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_48]), c_0_79])])).
% 0.20/0.40  cnf(c_0_122, plain, (k1_relat_1(X1)=k3_enumset1(X2,X2,X2,X2,X2)|k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_118, c_0_45])).
% 0.20/0.40  cnf(c_0_123, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_69]), c_0_79])])).
% 0.20/0.40  cnf(c_0_124, negated_conjecture, (k9_relat_1(esk7_0,X1)=k1_xboole_0|~r1_tarski(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_79]), c_0_48])])).
% 0.20/0.40  cnf(c_0_125, negated_conjecture, (esk7_0=k1_xboole_0|~v1_xboole_0(k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_102]), c_0_79])])).
% 0.20/0.40  cnf(c_0_126, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_78]), c_0_79])]), c_0_123])).
% 0.20/0.40  cnf(c_0_127, negated_conjecture, (~r1_tarski(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_124]), c_0_62])])).
% 0.20/0.40  cnf(c_0_128, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126]), c_0_48])])).
% 0.20/0.40  cnf(c_0_129, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128]), c_0_62])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 130
% 0.20/0.40  # Proof object clause steps            : 80
% 0.20/0.40  # Proof object formula steps           : 50
% 0.20/0.40  # Proof object conjectures             : 27
% 0.20/0.40  # Proof object clause conjectures      : 24
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 29
% 0.20/0.40  # Proof object initial formulas used   : 25
% 0.20/0.40  # Proof object generating inferences   : 44
% 0.20/0.40  # Proof object simplifying inferences  : 83
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 26
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 42
% 0.20/0.40  # Removed in clause preprocessing      : 4
% 0.20/0.40  # Initial clauses in saturation        : 38
% 0.20/0.40  # Processed clauses                    : 563
% 0.20/0.40  # ...of these trivial                  : 2
% 0.20/0.40  # ...subsumed                          : 292
% 0.20/0.40  # ...remaining for further processing  : 269
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 17
% 0.20/0.40  # Backward-rewritten                   : 107
% 0.20/0.40  # Generated clauses                    : 1593
% 0.20/0.40  # ...of the previous two non-trivial   : 1093
% 0.20/0.40  # Contextual simplify-reflections      : 5
% 0.20/0.40  # Paramodulations                      : 1591
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
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
% 0.20/0.40  # Current number of processed clauses  : 143
% 0.20/0.40  #    Positive orientable unit clauses  : 24
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 4
% 0.20/0.40  #    Non-unit-clauses                  : 115
% 0.20/0.40  # Current number of unprocessed clauses: 532
% 0.20/0.40  # ...number of literals in the above   : 1589
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 128
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 5046
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 3937
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 184
% 0.20/0.40  # Unit Clause-clause subsumption calls : 655
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 38
% 0.20/0.40  # BW rewrite match successes           : 19
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 19655
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.061 s
% 0.20/0.41  # System time              : 0.004 s
% 0.20/0.41  # Total time               : 0.065 s
% 0.20/0.41  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
