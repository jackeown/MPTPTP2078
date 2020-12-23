%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:04 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  110 (3839 expanded)
%              Number of clauses        :   81 (1897 expanded)
%              Number of leaves         :   14 ( 930 expanded)
%              Depth                    :   27
%              Number of atoms          :  297 (11803 expanded)
%              Number of equality atoms :   48 (1853 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(c_0_14,plain,(
    ! [X16] :
      ( ( r1_xboole_0(X16,X16)
        | X16 != k1_xboole_0 )
      & ( X16 = k1_xboole_0
        | ~ r1_xboole_0(X16,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X18)
      | ~ r1_tarski(X18,X17)
      | ~ r1_xboole_0(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

fof(c_0_32,plain,(
    ! [X26] :
      ( ~ v1_xboole_0(X26)
      | v1_xboole_0(k1_relat_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

cnf(c_0_33,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35])).

cnf(c_0_39,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X1)
    | ~ v1_xboole_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34])])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_44])).

fof(c_0_46,plain,(
    ! [X27] :
      ( v1_xboole_0(X27)
      | ~ v1_relat_1(X27)
      | ~ v1_xboole_0(k2_relat_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k1_xboole_0)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_45])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_50,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r1_tarski(k2_relat_1(esk4_0),esk3_0)
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k1_relat_1(k1_relat_1(k1_xboole_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_42])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_44])).

fof(c_0_56,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k1_relat_1(X33),X31)
      | ~ r1_tarski(k2_relat_1(X33),X32)
      | m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_45])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_61])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_68,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X36 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != k1_xboole_0
        | v1_funct_2(X36,X34,X35)
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_53]),c_0_54])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_1(k2_relat_1(esk4_0)),esk3_0)
    | v1_xboole_0(k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_42])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ r1_xboole_0(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_34])])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_37]),c_0_34])])).

cnf(c_0_74,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

fof(c_0_76,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk4_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_71])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_37]),c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ r1_tarski(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_80,plain,(
    ! [X19,X20] :
      ( ~ v1_xboole_0(X19)
      | X19 = X20
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk4_0),esk3_0,esk4_0) != k1_relat_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_70]),c_0_75])).

cnf(c_0_82,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ r1_tarski(esk3_0,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_70])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1)
    | ~ r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_58])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ r1_xboole_0(esk3_0,esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_67]),c_0_27])])).

cnf(c_0_89,plain,
    ( r1_xboole_0(X1,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_85]),c_0_31])])).

cnf(c_0_90,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_86]),c_0_27])])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_86]),c_0_34])])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r1_xboole_0(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_67]),c_0_31])])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ r1_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_67])).

cnf(c_0_96,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_91]),c_0_54]),c_0_92])])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_58])).

cnf(c_0_99,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r1_tarski(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_73])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_73])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_86]),c_0_34])])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_86]),c_0_27])])).

cnf(c_0_104,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_86])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_82]),c_0_97])])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_91])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_85]),c_0_106])])]),c_0_31])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.81/5.00  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 4.81/5.00  # and selection function PSelectUnlessUniqMaxPos.
% 4.81/5.00  #
% 4.81/5.00  # Preprocessing time       : 0.028 s
% 4.81/5.00  # Presaturation interreduction done
% 4.81/5.00  
% 4.81/5.00  # Proof found!
% 4.81/5.00  # SZS status Theorem
% 4.81/5.00  # SZS output start CNFRefutation
% 4.81/5.00  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.81/5.00  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.81/5.00  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.81/5.00  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.81/5.00  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.81/5.01  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.81/5.01  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.81/5.01  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.81/5.01  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 4.81/5.01  fof(t4_funct_2, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.81/5.01  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.81/5.01  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.81/5.01  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.81/5.01  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.81/5.01  fof(c_0_14, plain, ![X16]:((r1_xboole_0(X16,X16)|X16!=k1_xboole_0)&(X16=k1_xboole_0|~r1_xboole_0(X16,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 4.81/5.01  fof(c_0_15, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.81/5.01  fof(c_0_16, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 4.81/5.01  fof(c_0_17, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.81/5.01  fof(c_0_18, plain, ![X17, X18]:(v1_xboole_0(X18)|(~r1_tarski(X18,X17)|~r1_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 4.81/5.01  cnf(c_0_19, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.81/5.01  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.81/5.01  fof(c_0_21, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 4.81/5.01  fof(c_0_22, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 4.81/5.01  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.81/5.01  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.81/5.01  cnf(c_0_25, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.81/5.01  cnf(c_0_26, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_19])).
% 4.81/5.01  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 4.81/5.01  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.81/5.01  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.81/5.01  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 4.81/5.01  cnf(c_0_31, plain, (v1_xboole_0(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 4.81/5.01  fof(c_0_32, plain, ![X26]:(~v1_xboole_0(X26)|v1_xboole_0(k1_relat_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 4.81/5.01  cnf(c_0_33, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 4.81/5.01  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.81/5.01  cnf(c_0_35, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.81/5.01  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 4.81/5.01  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.81/5.01  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_30, c_0_35])).
% 4.81/5.01  cnf(c_0_39, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(X2,X1)|~v1_xboole_0(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_34])])).
% 4.81/5.01  cnf(c_0_40, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 4.81/5.01  cnf(c_0_41, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.81/5.01  cnf(c_0_42, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.81/5.01  cnf(c_0_43, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 4.81/5.01  cnf(c_0_44, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 4.81/5.01  cnf(c_0_45, plain, (r1_tarski(k1_relat_1(k1_relat_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_44])).
% 4.81/5.01  fof(c_0_46, plain, ![X27]:(v1_xboole_0(X27)|~v1_relat_1(X27)|~v1_xboole_0(k2_relat_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 4.81/5.01  fof(c_0_47, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))))), inference(assume_negation,[status(cth)],[t4_funct_2])).
% 4.81/5.01  cnf(c_0_48, plain, (~r2_hidden(X1,k1_relat_1(k1_relat_1(k1_xboole_0)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_39, c_0_45])).
% 4.81/5.01  cnf(c_0_49, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 4.81/5.01  fof(c_0_50, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r1_tarski(k2_relat_1(esk4_0),esk3_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).
% 4.81/5.01  cnf(c_0_51, plain, (v1_xboole_0(k1_relat_1(k1_relat_1(k1_xboole_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_42])).
% 4.81/5.01  cnf(c_0_52, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_30])).
% 4.81/5.01  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.81/5.01  cnf(c_0_54, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.81/5.01  cnf(c_0_55, plain, (v1_xboole_0(k1_relat_1(k1_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_51, c_0_44])).
% 4.81/5.01  fof(c_0_56, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k1_relat_1(X33),X31)|~r1_tarski(k2_relat_1(X33),X32)|m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 4.81/5.01  cnf(c_0_57, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 4.81/5.01  cnf(c_0_58, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_relat_1(k1_relat_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_45])])).
% 4.81/5.01  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 4.81/5.01  cnf(c_0_60, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.81/5.01  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk4_0)|~r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 4.81/5.01  cnf(c_0_62, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.81/5.01  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.81/5.01  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_59, c_0_27])).
% 4.81/5.01  cnf(c_0_65, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_53])).
% 4.81/5.01  cnf(c_0_66, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_38, c_0_61])).
% 4.81/5.01  cnf(c_0_67, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.81/5.01  fof(c_0_68, plain, ![X34, X35, X36]:((((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&((~v1_funct_2(X36,X34,X35)|X36=k1_xboole_0|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X36!=k1_xboole_0|v1_funct_2(X36,X34,X35)|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 4.81/5.01  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 4.81/5.01  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_53]), c_0_54])])).
% 4.81/5.01  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_1(k2_relat_1(esk4_0)),esk3_0)|v1_xboole_0(k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_65, c_0_42])).
% 4.81/5.01  cnf(c_0_72, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~r1_xboole_0(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_34])])).
% 4.81/5.01  cnf(c_0_73, plain, (r1_xboole_0(X1,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_37]), c_0_34])])).
% 4.81/5.01  cnf(c_0_74, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 4.81/5.01  cnf(c_0_75, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 4.81/5.01  fof(c_0_76, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k1_relset_1(X28,X29,X30)=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 4.81/5.01  cnf(c_0_77, negated_conjecture, (v1_xboole_0(k2_relat_1(esk4_0))|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_71])).
% 4.81/5.01  cnf(c_0_78, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_relat_1(X2))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_37]), c_0_38])).
% 4.81/5.01  cnf(c_0_79, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~r1_tarski(esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 4.81/5.01  fof(c_0_80, plain, ![X19, X20]:(~v1_xboole_0(X19)|X19=X20|~v1_xboole_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 4.81/5.01  cnf(c_0_81, negated_conjecture, (esk3_0=k1_xboole_0|k1_relset_1(k1_relat_1(esk4_0),esk3_0,esk4_0)!=k1_relat_1(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_70]), c_0_75])).
% 4.81/5.01  cnf(c_0_82, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 4.81/5.01  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_77])).
% 4.81/5.01  cnf(c_0_84, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~r1_tarski(esk3_0,k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 4.81/5.01  cnf(c_0_85, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 4.81/5.01  cnf(c_0_86, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_70])])).
% 4.81/5.01  cnf(c_0_87, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)|~r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_83, c_0_58])).
% 4.81/5.01  cnf(c_0_88, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~r1_xboole_0(esk3_0,esk3_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_67]), c_0_27])])).
% 4.81/5.01  cnf(c_0_89, plain, (r1_xboole_0(X1,X1)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_85]), c_0_31])])).
% 4.81/5.01  cnf(c_0_90, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 4.81/5.01  cnf(c_0_91, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_86]), c_0_27])])).
% 4.81/5.01  cnf(c_0_92, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_86]), c_0_34])])).
% 4.81/5.01  cnf(c_0_93, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 4.81/5.01  cnf(c_0_94, negated_conjecture, (v1_xboole_0(esk4_0)|~r1_xboole_0(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_67]), c_0_31])])).
% 4.81/5.01  cnf(c_0_95, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~r1_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_75, c_0_67])).
% 4.81/5.01  cnf(c_0_96, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_90])).
% 4.81/5.01  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_91]), c_0_54]), c_0_92])])).
% 4.81/5.01  cnf(c_0_98, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~r1_tarski(esk3_0,k1_relat_1(k1_relat_1(k1_xboole_0)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_93, c_0_58])).
% 4.81/5.01  cnf(c_0_99, negated_conjecture, (v1_xboole_0(esk4_0)|~r1_tarski(esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_94, c_0_73])).
% 4.81/5.01  cnf(c_0_100, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~r1_tarski(k1_relat_1(esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_95, c_0_73])).
% 4.81/5.01  cnf(c_0_101, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 4.81/5.01  cnf(c_0_102, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_86]), c_0_34])])).
% 4.81/5.01  cnf(c_0_103, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_86]), c_0_27])])).
% 4.81/5.01  cnf(c_0_104, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k1_relat_1(esk4_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_100, c_0_86])).
% 4.81/5.01  cnf(c_0_105, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|k1_relat_1(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_82]), c_0_97])])).
% 4.81/5.01  cnf(c_0_106, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 4.81/5.01  cnf(c_0_107, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_91])])).
% 4.81/5.01  cnf(c_0_108, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_85]), c_0_106])])]), c_0_31])])).
% 4.81/5.01  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108])]), ['proof']).
% 4.81/5.01  # SZS output end CNFRefutation
% 4.81/5.01  # Proof object total steps             : 110
% 4.81/5.01  # Proof object clause steps            : 81
% 4.81/5.01  # Proof object formula steps           : 29
% 4.81/5.01  # Proof object conjectures             : 42
% 4.81/5.01  # Proof object clause conjectures      : 39
% 4.81/5.01  # Proof object formula conjectures     : 3
% 4.81/5.01  # Proof object initial clauses used    : 22
% 4.81/5.01  # Proof object initial formulas used   : 14
% 4.81/5.01  # Proof object generating inferences   : 47
% 4.81/5.01  # Proof object simplifying inferences  : 59
% 4.81/5.01  # Training examples: 0 positive, 0 negative
% 4.81/5.01  # Parsed axioms                        : 14
% 4.81/5.01  # Removed by relevancy pruning/SinE    : 0
% 4.81/5.01  # Initial clauses                      : 29
% 4.81/5.01  # Removed in clause preprocessing      : 0
% 4.81/5.01  # Initial clauses in saturation        : 29
% 4.81/5.01  # Processed clauses                    : 36626
% 4.81/5.01  # ...of these trivial                  : 422
% 4.81/5.01  # ...subsumed                          : 31652
% 4.81/5.01  # ...remaining for further processing  : 4552
% 4.81/5.01  # Other redundant clauses eliminated   : 179
% 4.81/5.01  # Clauses deleted for lack of memory   : 0
% 4.81/5.01  # Backward-subsumed                    : 157
% 4.81/5.01  # Backward-rewritten                   : 486
% 4.81/5.01  # Generated clauses                    : 934313
% 4.81/5.01  # ...of the previous two non-trivial   : 869965
% 4.81/5.01  # Contextual simplify-reflections      : 125
% 4.81/5.01  # Paramodulations                      : 933904
% 4.81/5.01  # Factorizations                       : 231
% 4.81/5.01  # Equation resolutions                 : 179
% 4.81/5.01  # Propositional unsat checks           : 0
% 4.81/5.01  #    Propositional check models        : 0
% 4.81/5.01  #    Propositional check unsatisfiable : 0
% 4.81/5.01  #    Propositional clauses             : 0
% 4.81/5.01  #    Propositional clauses after purity: 0
% 4.81/5.01  #    Propositional unsat core size     : 0
% 4.81/5.01  #    Propositional preprocessing time  : 0.000
% 4.81/5.01  #    Propositional encoding time       : 0.000
% 4.81/5.01  #    Propositional solver time         : 0.000
% 4.81/5.01  #    Success case prop preproc time    : 0.000
% 4.81/5.01  #    Success case prop encoding time   : 0.000
% 4.81/5.01  #    Success case prop solver time     : 0.000
% 4.81/5.01  # Current number of processed clauses  : 3874
% 4.81/5.01  #    Positive orientable unit clauses  : 1057
% 4.81/5.01  #    Positive unorientable unit clauses: 0
% 4.81/5.01  #    Negative unit clauses             : 1659
% 4.81/5.01  #    Non-unit-clauses                  : 1158
% 4.81/5.01  # Current number of unprocessed clauses: 817131
% 4.81/5.01  # ...number of literals in the above   : 2668889
% 4.81/5.01  # Current number of archived formulas  : 0
% 4.81/5.01  # Current number of archived clauses   : 671
% 4.81/5.01  # Clause-clause subsumption calls (NU) : 527807
% 4.81/5.01  # Rec. Clause-clause subsumption calls : 247853
% 4.81/5.01  # Non-unit clause-clause subsumptions  : 21075
% 4.81/5.01  # Unit Clause-clause subsumption calls : 238289
% 4.81/5.01  # Rewrite failures with RHS unbound    : 0
% 4.81/5.01  # BW rewrite match attempts            : 69381
% 4.81/5.01  # BW rewrite match successes           : 100
% 4.81/5.01  # Condensation attempts                : 0
% 4.81/5.01  # Condensation successes               : 0
% 4.81/5.01  # Termbank termtop insertions          : 11718233
% 4.81/5.03  
% 4.81/5.03  # -------------------------------------------------
% 4.81/5.03  # User time                : 4.424 s
% 4.81/5.03  # System time              : 0.265 s
% 4.81/5.03  # Total time               : 4.689 s
% 4.81/5.03  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
