%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 199 expanded)
%              Number of clauses        :   44 (  92 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  173 ( 535 expanded)
%              Number of equality atoms :   27 (  84 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ~ ( k2_relset_1(X2,X1,X3) != k1_xboole_0
                  & ! [X4] :
                      ( m1_subset_1(X4,X2)
                     => ~ r2_hidden(X4,k1_relset_1(X2,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(fc11_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ~ ( k2_relset_1(X2,X1,X3) != k1_xboole_0
                    & ! [X4] :
                        ( m1_subset_1(X4,X2)
                       => ~ r2_hidden(X4,k1_relset_1(X2,X1,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_relset_1])).

fof(c_0_17,plain,(
    ! [X11] : m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_18,plain,(
    ! [X10] : k2_subset_1(X10) = X10 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_19,plain,(
    ! [X16] :
      ( ~ v1_xboole_0(X16)
      | v1_xboole_0(k2_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).

fof(c_0_20,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X39)))
      | ~ r1_tarski(k1_relat_1(X40),X38)
      | m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

fof(c_0_22,negated_conjecture,(
    ! [X44] :
      ( ~ v1_xboole_0(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
      & k2_relset_1(esk3_0,esk2_0,esk4_0) != k1_xboole_0
      & ( ~ m1_subset_1(X44,esk3_0)
        | ~ r2_hidden(X44,k1_relset_1(esk3_0,esk2_0,esk4_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

fof(c_0_23,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | v1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_xboole_0(X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_xboole_0(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v4_relat_1(X18,X17)
      | X18 = k7_relat_1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_40,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_45,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,X20)
        | ~ r2_hidden(X19,k1_relat_1(k7_relat_1(X21,X20)))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(X19,k1_relat_1(X21))
        | ~ r2_hidden(X19,k1_relat_1(k7_relat_1(X21,X20)))
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X19,X20)
        | ~ r2_hidden(X19,k1_relat_1(X21))
        | r2_hidden(X19,k1_relat_1(k7_relat_1(X21,X20)))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_46,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_48,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = esk4_0
    | ~ v4_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( v4_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_1(k1_relat_1(esk4_0)),k1_relat_1(esk4_0))
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_52])).

fof(c_0_60,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_1(k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_58])).

cnf(c_0_65,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_59])).

cnf(c_0_66,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_67,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_1(k1_relat_1(esk4_0)),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relset_1(esk3_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(esk3_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_32])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_1(k1_relat_1(esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( ~ m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk1_1(k1_relat_1(esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:33:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.20/0.38  # and selection function SelectCQIArEqFirst.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t50_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>~((k2_relset_1(X2,X1,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k1_relset_1(X2,X1,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 0.20/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.38  fof(fc11_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 0.20/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.38  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.38  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.20/0.38  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.20/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.38  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.20/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>~((k2_relset_1(X2,X1,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k1_relset_1(X2,X1,X3)))))))))), inference(assume_negation,[status(cth)],[t50_relset_1])).
% 0.20/0.38  fof(c_0_17, plain, ![X11]:m1_subset_1(k2_subset_1(X11),k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.38  fof(c_0_18, plain, ![X10]:k2_subset_1(X10)=X10, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.38  fof(c_0_19, plain, ![X16]:(~v1_xboole_0(X16)|v1_xboole_0(k2_relat_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).
% 0.20/0.38  fof(c_0_20, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X37, X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X39)))|(~r1_tarski(k1_relat_1(X40),X38)|m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.20/0.38  fof(c_0_22, negated_conjecture, ![X44]:(~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))&(k2_relset_1(esk3_0,esk2_0,esk4_0)!=k1_xboole_0&(~m1_subset_1(X44,esk3_0)|~r2_hidden(X44,k1_relset_1(esk3_0,esk2_0,esk4_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.20/0.38  fof(c_0_23, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  cnf(c_0_24, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_25, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_26, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.38  cnf(c_0_27, plain, (v1_xboole_0(k2_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_29, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|v1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.38  fof(c_0_30, plain, ![X28, X29, X30]:(~v1_xboole_0(X28)|(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_xboole_0(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.20/0.38  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  cnf(c_0_35, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_36, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  fof(c_0_37, plain, ![X17, X18]:(~v1_relat_1(X18)|~v4_relat_1(X18,X17)|X18=k7_relat_1(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.20/0.38  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  fof(c_0_39, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.38  fof(c_0_40, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.38  cnf(c_0_41, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.38  cnf(c_0_44, plain, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  fof(c_0_45, plain, ![X19, X20, X21]:(((r2_hidden(X19,X20)|~r2_hidden(X19,k1_relat_1(k7_relat_1(X21,X20)))|~v1_relat_1(X21))&(r2_hidden(X19,k1_relat_1(X21))|~r2_hidden(X19,k1_relat_1(k7_relat_1(X21,X20)))|~v1_relat_1(X21)))&(~r2_hidden(X19,X20)|~r2_hidden(X19,k1_relat_1(X21))|r2_hidden(X19,k1_relat_1(k7_relat_1(X21,X20)))|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.20/0.38  cnf(c_0_46, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 0.20/0.38  cnf(c_0_48, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_49, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_50, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_28])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  cnf(c_0_52, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_44])).
% 0.20/0.38  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (k7_relat_1(esk4_0,X1)=esk4_0|~v4_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (v4_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_32])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_32])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_1(k1_relat_1(esk4_0)),k1_relat_1(esk4_0))|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.38  cnf(c_0_59, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_52])).
% 0.20/0.38  fof(c_0_60, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_47])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_1(k1_relat_1(esk4_0)),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_58])).
% 0.20/0.38  cnf(c_0_65, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_35, c_0_59])).
% 0.20/0.38  cnf(c_0_66, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.38  fof(c_0_67, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (r2_hidden(esk1_1(k1_relat_1(esk4_0)),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (~m1_subset_1(X1,esk3_0)|~r2_hidden(X1,k1_relset_1(esk3_0,esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (k1_relset_1(esk3_0,esk2_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_32])).
% 0.20/0.38  cnf(c_0_72, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_1(k1_relat_1(esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (~m1_subset_1(X1,esk3_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk1_1(k1_relat_1(esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_69])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 77
% 0.20/0.38  # Proof object clause steps            : 44
% 0.20/0.38  # Proof object formula steps           : 33
% 0.20/0.38  # Proof object conjectures             : 24
% 0.20/0.38  # Proof object clause conjectures      : 21
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 18
% 0.20/0.38  # Proof object initial formulas used   : 16
% 0.20/0.38  # Proof object generating inferences   : 23
% 0.20/0.38  # Proof object simplifying inferences  : 6
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 16
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 25
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 24
% 0.20/0.38  # Processed clauses                    : 229
% 0.20/0.38  # ...of these trivial                  : 14
% 0.20/0.38  # ...subsumed                          : 59
% 0.20/0.38  # ...remaining for further processing  : 156
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 3
% 0.20/0.38  # Backward-rewritten                   : 16
% 0.20/0.38  # Generated clauses                    : 1231
% 0.20/0.38  # ...of the previous two non-trivial   : 753
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 1231
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 113
% 0.20/0.38  #    Positive orientable unit clauses  : 31
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 78
% 0.20/0.38  # Current number of unprocessed clauses: 531
% 0.20/0.38  # ...number of literals in the above   : 1889
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 44
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1167
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 782
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 61
% 0.20/0.38  # Unit Clause-clause subsumption calls : 115
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 13
% 0.20/0.38  # BW rewrite match successes           : 5
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 16235
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.041 s
% 0.20/0.38  # System time              : 0.008 s
% 0.20/0.38  # Total time               : 0.049 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
