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
% DateTime   : Thu Dec  3 10:58:15 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 192 expanded)
%              Number of clauses        :   36 (  84 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 720 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                <=> ? [X5] :
                      ( m1_subset_1(X5,X2)
                      & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relset_1])).

fof(c_0_14,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
      | ~ r1_tarski(k2_relat_1(X43),X41)
      | m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

fof(c_0_15,negated_conjecture,(
    ! [X48] :
      ( ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
      & ( ~ r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0))
        | ~ m1_subset_1(X48,esk4_0)
        | ~ r2_hidden(k4_tarski(X48,esk6_0),esk5_0) )
      & ( m1_subset_1(esk7_0,esk4_0)
        | r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0)) )
      & ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)
        | r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_relset_1(X37,X38,X39) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_20,plain,(
    ! [X34,X35,X36] :
      ( ( v4_relat_1(X36,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v5_relat_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_21,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v4_relat_1(X30,X29)
      | X30 = k7_relat_1(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_27,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X14,X15,X16,X17] :
      ( ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) )
      & ( r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) )
      & ( ~ r2_hidden(X14,X16)
        | ~ r2_hidden(X15,X17)
        | r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk4_0,X1))
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0))
    | ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X1,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(esk4_0,esk3_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

fof(c_0_34,plain,(
    ! [X22,X23,X24,X26] :
      ( ( r2_hidden(esk2_3(X22,X23,X24),k1_relat_1(X24))
        | ~ r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk2_3(X22,X23,X24),X22),X24)
        | ~ r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X23)
        | ~ r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X26,k1_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X26,X22),X24)
        | ~ r2_hidden(X26,X23)
        | r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_35,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k2_relat_1(k7_relat_1(X28,X27)) = k9_relat_1(X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_36,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( v4_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk4_0,X2))
    | ~ r2_hidden(X1,esk5_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)
    | r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_42,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(k4_tarski(X1,esk6_0),esk5_0)
    | ~ r2_hidden(esk6_0,k2_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k7_relat_1(esk5_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),esk5_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)
    | r2_hidden(esk6_0,k2_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X18,X19] :
      ( ~ r2_hidden(X18,X19)
      | m1_subset_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk6_0,X1,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))
    | ~ r2_hidden(esk6_0,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38])])).

cnf(c_0_52,negated_conjecture,
    ( k9_relat_1(esk5_0,esk4_0) = k2_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_38])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_30])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk6_0,esk4_0,esk5_0),esk4_0)
    | ~ r2_hidden(esk6_0,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk6_0,esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk2_3(X1,esk4_0,esk5_0),esk4_0)
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_52]),c_0_38])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:35:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.029 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t48_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 0.19/0.37  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.19/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.37  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.37  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3))))))), inference(assume_negation,[status(cth)],[t48_relset_1])).
% 0.19/0.37  fof(c_0_14, plain, ![X40, X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))|(~r1_tarski(k2_relat_1(X43),X41)|m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X41))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.19/0.37  fof(c_0_15, negated_conjecture, ![X48]:(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))&((~r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0))|(~m1_subset_1(X48,esk4_0)|~r2_hidden(k4_tarski(X48,esk6_0),esk5_0)))&((m1_subset_1(esk7_0,esk4_0)|r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0)))&(r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)|r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).
% 0.19/0.37  fof(c_0_16, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  fof(c_0_19, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k2_relset_1(X37,X38,X39)=k2_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.37  fof(c_0_20, plain, ![X34, X35, X36]:((v4_relat_1(X36,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(v5_relat_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.37  fof(c_0_21, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.37  fof(c_0_22, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  cnf(c_0_25, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  fof(c_0_26, plain, ![X29, X30]:(~v1_relat_1(X30)|~v4_relat_1(X30,X29)|X30=k7_relat_1(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.19/0.37  cnf(c_0_27, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  fof(c_0_29, plain, ![X14, X15, X16, X17]:(((r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)))&(r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17))))&(~r2_hidden(X14,X16)|~r2_hidden(X15,X17)|r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk4_0,X1))|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0))|~m1_subset_1(X1,esk4_0)|~r2_hidden(k4_tarski(X1,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (k2_relset_1(esk4_0,esk3_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.19/0.37  fof(c_0_34, plain, ![X22, X23, X24, X26]:((((r2_hidden(esk2_3(X22,X23,X24),k1_relat_1(X24))|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk2_3(X22,X23,X24),X22),X24)|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24)))&(r2_hidden(esk2_3(X22,X23,X24),X23)|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24)))&(~r2_hidden(X26,k1_relat_1(X24))|~r2_hidden(k4_tarski(X26,X22),X24)|~r2_hidden(X26,X23)|r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.37  fof(c_0_35, plain, ![X27, X28]:(~v1_relat_1(X28)|k2_relat_1(k7_relat_1(X28,X27))=k9_relat_1(X28,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.37  cnf(c_0_36, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (v4_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_18])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.19/0.37  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk4_0,X2))|~r2_hidden(X1,esk5_0)|~r1_tarski(k2_relat_1(esk5_0),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)|r2_hidden(esk6_0,k2_relset_1(esk4_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  fof(c_0_42, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (~m1_subset_1(X1,esk4_0)|~r2_hidden(k4_tarski(X1,esk6_0),esk5_0)|~r2_hidden(esk6_0,k2_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_44, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_45, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (k7_relat_1(esk5_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),esk5_0)|~r1_tarski(k2_relat_1(esk5_0),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)|r2_hidden(esk6_0,k2_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_41, c_0_33])).
% 0.19/0.37  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.37  fof(c_0_50, plain, ![X18, X19]:(~r2_hidden(X18,X19)|m1_subset_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (~m1_subset_1(esk2_3(esk6_0,X1,esk5_0),esk4_0)|~r2_hidden(esk6_0,k9_relat_1(esk5_0,X1))|~r2_hidden(esk6_0,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_38])])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (k9_relat_1(esk5_0,esk4_0)=k2_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_38])])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (r2_hidden(esk6_0,X1)|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_30])).
% 0.19/0.37  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.37  cnf(c_0_55, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.37  cnf(c_0_56, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (~m1_subset_1(esk2_3(esk6_0,esk4_0,esk5_0),esk4_0)|~r2_hidden(esk6_0,k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.37  cnf(c_0_59, plain, (m1_subset_1(esk2_3(X1,X2,X3),X2)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (~m1_subset_1(esk2_3(esk6_0,esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk2_3(X1,esk4_0,esk5_0),esk4_0)|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_52]), c_0_38])])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_58])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 63
% 0.19/0.37  # Proof object clause steps            : 36
% 0.19/0.37  # Proof object formula steps           : 27
% 0.19/0.37  # Proof object conjectures             : 24
% 0.19/0.37  # Proof object clause conjectures      : 21
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 16
% 0.19/0.37  # Proof object initial formulas used   : 13
% 0.19/0.37  # Proof object generating inferences   : 16
% 0.19/0.37  # Proof object simplifying inferences  : 16
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 13
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 29
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 29
% 0.19/0.37  # Processed clauses                    : 122
% 0.19/0.37  # ...of these trivial                  : 2
% 0.19/0.37  # ...subsumed                          : 16
% 0.19/0.37  # ...remaining for further processing  : 104
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 11
% 0.19/0.37  # Backward-rewritten                   : 16
% 0.19/0.37  # Generated clauses                    : 141
% 0.19/0.37  # ...of the previous two non-trivial   : 131
% 0.19/0.37  # Contextual simplify-reflections      : 3
% 0.19/0.37  # Paramodulations                      : 139
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 75
% 0.19/0.37  #    Positive orientable unit clauses  : 20
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 52
% 0.19/0.37  # Current number of unprocessed clauses: 38
% 0.19/0.37  # ...number of literals in the above   : 116
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 27
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 452
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 423
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 22
% 0.19/0.37  # Unit Clause-clause subsumption calls : 97
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 14
% 0.19/0.37  # BW rewrite match successes           : 6
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3941
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.034 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.039 s
% 0.19/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
