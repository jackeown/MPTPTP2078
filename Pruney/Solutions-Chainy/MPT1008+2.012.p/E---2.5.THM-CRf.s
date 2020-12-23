%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:31 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 344 expanded)
%              Number of clauses        :   61 ( 146 expanded)
%              Number of leaves         :   20 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  237 ( 719 expanded)
%              Number of equality atoms :   92 ( 312 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))
    & esk4_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X45,X46,X47] :
      ( ( v4_relat_1(X47,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v5_relat_1(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | v1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_29,plain,(
    ! [X21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_30,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v4_relat_1(X38,X37)
      | X38 = k7_relat_1(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_31,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | k1_relat_1(X41) != k1_tarski(X40)
      | k2_relat_1(X41) = k1_tarski(k1_funct_1(X41,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_36,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | k11_relat_1(X29,X30) = k9_relat_1(X29,k1_tarski(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_37,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | k2_relat_1(k7_relat_1(X34,X33)) = k9_relat_1(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_38,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v4_relat_1(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_41,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_42,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_relset_1(X51,X52,X53) = k1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_44,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X60,X61,X62,X63] :
      ( ~ v1_funct_1(X63)
      | ~ v1_funct_2(X63,X60,X61)
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | ~ r2_hidden(X62,X60)
      | X61 = k1_xboole_0
      | r2_hidden(k1_funct_1(X63,X62),k2_relset_1(X60,X61,X63)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_48,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | k2_relset_1(X54,X55,X56) = k2_relat_1(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_49,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_52,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_41]),c_0_42])])).

cnf(c_0_53,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_54,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X7
        | X10 = X8
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( esk1_3(X12,X13,X14) != X12
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( esk1_3(X12,X13,X14) != X13
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | esk1_3(X12,X13,X14) = X12
        | esk1_3(X12,X13,X14) = X13
        | X14 = k2_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_55,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | m1_subset_1(k1_relset_1(X48,X49,X50),k1_zfmisc_1(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_56,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) != k1_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_58,plain,
    ( k2_relat_1(X1) = k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k1_enumset1(X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_60,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_26]),c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_64,plain,(
    ! [X35,X36] :
      ( ( ~ r2_hidden(X35,k1_relat_1(X36))
        | k11_relat_1(X36,X35) != k1_xboole_0
        | ~ v1_relat_1(X36) )
      & ( k11_relat_1(X36,X35) = k1_xboole_0
        | r2_hidden(X35,k1_relat_1(X36))
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_65,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_enumset1(X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_26]),c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( k9_relat_1(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_40])])).

cnf(c_0_67,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_52]),c_0_53]),c_0_42])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_69,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) != k2_relat_1(esk5_0)
    | k1_enumset1(esk3_0,esk3_0,esk3_0) != k1_relat_1(esk5_0)
    | ~ v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

fof(c_0_73,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(k1_tarski(X22),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0))
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_61]),c_0_59])]),c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_32])).

cnf(c_0_76,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( k11_relat_1(esk5_0,esk3_0) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_40])])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_79,plain,
    ( k11_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_67]),c_0_42])])).

cnf(c_0_80,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_27])).

fof(c_0_82,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_32]),c_0_71])).

cnf(c_0_85,negated_conjecture,
    ( k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) != k2_relat_1(esk5_0)
    | k1_enumset1(esk3_0,esk3_0,esk3_0) != k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_40])])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),k2_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_40])])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_42]),c_0_80])])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) != k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_75])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_26]),c_0_27])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:02:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.39  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.13/0.39  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.13/0.39  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.13/0.39  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.39  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 0.13/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.39  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.13/0.39  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.13/0.39  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))&(esk4_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.13/0.39  fof(c_0_22, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_23, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_24, plain, ![X45, X46, X47]:((v4_relat_1(X47,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(v5_relat_1(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  fof(c_0_28, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|v1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.39  fof(c_0_29, plain, ![X21]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.39  fof(c_0_30, plain, ![X37, X38]:(~v1_relat_1(X38)|~v4_relat_1(X38,X37)|X38=k7_relat_1(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.13/0.39  cnf(c_0_31, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.13/0.39  cnf(c_0_33, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_34, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  fof(c_0_35, plain, ![X40, X41]:(~v1_relat_1(X41)|~v1_funct_1(X41)|(k1_relat_1(X41)!=k1_tarski(X40)|k2_relat_1(X41)=k1_tarski(k1_funct_1(X41,X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.13/0.39  fof(c_0_36, plain, ![X29, X30]:(~v1_relat_1(X29)|k11_relat_1(X29,X30)=k9_relat_1(X29,k1_tarski(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.13/0.39  fof(c_0_37, plain, ![X33, X34]:(~v1_relat_1(X34)|k2_relat_1(k7_relat_1(X34,X33))=k9_relat_1(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.39  cnf(c_0_38, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (v4_relat_1(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.13/0.39  cnf(c_0_41, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_34])).
% 0.13/0.39  cnf(c_0_42, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.39  fof(c_0_43, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k1_relset_1(X51,X52,X53)=k1_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_45, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  fof(c_0_46, plain, ![X60, X61, X62, X63]:(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|(~r2_hidden(X62,X60)|(X61=k1_xboole_0|r2_hidden(k1_funct_1(X63,X62),k2_relset_1(X60,X61,X63))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  fof(c_0_48, plain, ![X54, X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|k2_relset_1(X54,X55,X56)=k2_relat_1(X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.39  cnf(c_0_49, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_50, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.13/0.39  cnf(c_0_52, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_41]), c_0_42])])).
% 0.13/0.39  cnf(c_0_53, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.39  fof(c_0_54, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(X10=X7|X10=X8)|X9!=k2_tarski(X7,X8))&((X11!=X7|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))))&(((esk1_3(X12,X13,X14)!=X12|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13))&(esk1_3(X12,X13,X14)!=X13|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(esk1_3(X12,X13,X14)=X12|esk1_3(X12,X13,X14)=X13)|X14=k2_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.39  fof(c_0_55, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|m1_subset_1(k1_relset_1(X48,X49,X50),k1_zfmisc_1(X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.13/0.39  cnf(c_0_56, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)!=k1_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.13/0.39  cnf(c_0_58, plain, (k2_relat_1(X1)=k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k1_enumset1(X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_60, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_26]), c_0_27])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_63, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  fof(c_0_64, plain, ![X35, X36]:((~r2_hidden(X35,k1_relat_1(X36))|k11_relat_1(X36,X35)!=k1_xboole_0|~v1_relat_1(X36))&(k11_relat_1(X36,X35)=k1_xboole_0|r2_hidden(X35,k1_relat_1(X36))|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.13/0.39  cnf(c_0_65, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_enumset1(X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_26]), c_0_27])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (k9_relat_1(esk5_0,k1_enumset1(esk3_0,esk3_0,esk3_0))=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_40])])).
% 0.13/0.39  cnf(c_0_67, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_52]), c_0_53]), c_0_42])])).
% 0.13/0.39  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  fof(c_0_69, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_70, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (k1_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_32])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)!=k2_relat_1(esk5_0)|k1_enumset1(esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk5_0)|~v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.13/0.39  fof(c_0_73, plain, ![X22, X23]:(~r2_hidden(X22,X23)|m1_subset_1(k1_tarski(X22),k1_zfmisc_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0))|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_32]), c_0_61]), c_0_59])]), c_0_62])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_32])).
% 0.13/0.39  cnf(c_0_76, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (k11_relat_1(esk5_0,esk3_0)=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_40])])).
% 0.13/0.39  cnf(c_0_78, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.39  cnf(c_0_79, plain, (k11_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_67]), c_0_42])])).
% 0.13/0.39  cnf(c_0_80, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.39  cnf(c_0_81, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_68, c_0_27])).
% 0.13/0.39  fof(c_0_82, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  cnf(c_0_83, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(k1_enumset1(esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_32]), c_0_71])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (k2_relset_1(k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)!=k2_relat_1(esk5_0)|k1_enumset1(esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_40])])).
% 0.13/0.39  cnf(c_0_86, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),k2_relat_1(esk5_0))|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.39  cnf(c_0_88, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_40])])).
% 0.13/0.39  cnf(c_0_89, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_42]), c_0_80])])).
% 0.13/0.39  cnf(c_0_90, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X3,X1)), inference(er,[status(thm)],[c_0_81])).
% 0.13/0.39  cnf(c_0_91, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.13/0.39  cnf(c_0_92, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.13/0.39  cnf(c_0_93, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_75])])).
% 0.13/0.39  cnf(c_0_94, plain, (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_26]), c_0_27])).
% 0.13/0.39  cnf(c_0_95, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.13/0.39  cnf(c_0_96, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[c_0_90])).
% 0.13/0.39  cnf(c_0_97, negated_conjecture, (~r1_tarski(k1_enumset1(esk3_0,esk3_0,esk3_0),k1_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.13/0.39  cnf(c_0_98, plain, (r1_tarski(k1_enumset1(X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_83, c_0_94])).
% 0.13/0.39  cnf(c_0_99, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.13/0.39  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 101
% 0.13/0.39  # Proof object clause steps            : 61
% 0.13/0.39  # Proof object formula steps           : 40
% 0.13/0.39  # Proof object conjectures             : 30
% 0.13/0.39  # Proof object clause conjectures      : 27
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 26
% 0.13/0.39  # Proof object initial formulas used   : 20
% 0.13/0.39  # Proof object generating inferences   : 24
% 0.13/0.39  # Proof object simplifying inferences  : 52
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 25
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 46
% 0.13/0.39  # Removed in clause preprocessing      : 2
% 0.13/0.39  # Initial clauses in saturation        : 44
% 0.13/0.39  # Processed clauses                    : 262
% 0.13/0.39  # ...of these trivial                  : 7
% 0.13/0.39  # ...subsumed                          : 42
% 0.13/0.39  # ...remaining for further processing  : 213
% 0.13/0.39  # Other redundant clauses eliminated   : 15
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 11
% 0.13/0.39  # Backward-rewritten                   : 17
% 0.13/0.39  # Generated clauses                    : 618
% 0.13/0.39  # ...of the previous two non-trivial   : 572
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 592
% 0.13/0.39  # Factorizations                       : 4
% 0.13/0.39  # Equation resolutions                 : 22
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 138
% 0.13/0.39  #    Positive orientable unit clauses  : 39
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 6
% 0.13/0.39  #    Non-unit-clauses                  : 93
% 0.13/0.39  # Current number of unprocessed clauses: 368
% 0.13/0.39  # ...number of literals in the above   : 1990
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 73
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1488
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 476
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 31
% 0.13/0.39  # Unit Clause-clause subsumption calls : 186
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 34
% 0.13/0.39  # BW rewrite match successes           : 6
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 14646
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.052 s
% 0.13/0.39  # System time              : 0.008 s
% 0.13/0.39  # Total time               : 0.059 s
% 0.13/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
