%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:28 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   99 (2859 expanded)
%              Number of clauses        :   72 (1125 expanded)
%              Number of leaves         :   13 ( 712 expanded)
%              Depth                    :   17
%              Number of atoms          :  305 (12763 expanded)
%              Number of equality atoms :   73 (2203 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_14,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,k1_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( X23 = k1_funct_1(X24,X22)
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(X22,k1_relat_1(X24))
        | X23 != k1_funct_1(X24,X22)
        | r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_15,plain,(
    ! [X17,X18,X19,X21] :
      ( ( r2_hidden(esk1_3(X17,X18,X19),k1_relat_1(X19))
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk1_3(X17,X18,X19),X17),X19)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(X21,k1_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X21,X17),X19)
        | ~ r2_hidden(X21,X18)
        | r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_17,negated_conjecture,(
    ! [X50] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))
      & ( ~ r2_hidden(X50,esk4_0)
        | ~ r2_hidden(X50,esk6_0)
        | esk8_0 != k1_funct_1(esk7_0,X50) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_18,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_19,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k7_relset_1(X31,X32,X33,X34) = k9_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_26,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X44 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != k1_xboole_0
        | v1_funct_2(X44,X42,X43)
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | esk8_0 != k1_funct_1(esk7_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_relset_1(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_36,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk6_0)
    | ~ r2_hidden(esk8_0,k9_relat_1(esk7_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,esk5_0,esk7_0))
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_31])])).

cnf(c_0_42,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk7_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk8_0,esk6_0,esk7_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk7_0),esk4_0)
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_45,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_46,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_40])])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

fof(c_0_57,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ r2_hidden(X10,X9)
      | r2_hidden(X10,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_58,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,k1_xboole_0,esk7_0))
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_48])).

cnf(c_0_60,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_54])).

cnf(c_0_65,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0))
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_54])).

cnf(c_0_69,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relset_1(X3,X4,k1_xboole_0))
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_64]),c_0_65])])).

cnf(c_0_71,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r2_hidden(esk1_3(esk8_0,esk6_0,esk7_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_56])).

cnf(c_0_72,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,esk7_0),k1_xboole_0)
    | ~ r2_hidden(X1,k9_relat_1(esk7_0,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_73,plain,(
    ! [X35,X36,X37,X39,X40] :
      ( ( r2_hidden(esk2_3(X35,X36,X37),X36)
        | k1_relset_1(X36,X35,X37) = X36
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35))) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X35,X36,X37),X39),X37)
        | k1_relset_1(X36,X35,X37) = X36
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35))) )
      & ( k1_relset_1(X36,X35,X37) != X36
        | ~ r2_hidden(X40,X36)
        | r2_hidden(k4_tarski(X40,esk3_4(X35,X36,X37,X40)),X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_74,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_75,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_76,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,k1_xboole_0),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_21]),c_0_65])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_3(X1,X4,X2),X3)
    | ~ r2_hidden(X1,k9_relat_1(X2,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_21]),c_0_34])).

cnf(c_0_78,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_64])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_40])])).

cnf(c_0_80,plain,
    ( k1_relset_1(X2,X1,X3) = X2
    | ~ r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X4),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | k1_relset_1(X2,X1,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_84,plain,
    ( k1_funct_1(X1,esk1_3(X2,X3,k1_xboole_0)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_76])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))
    | ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_65])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_79])).

cnf(c_0_87,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(esk2_3(X2,X1,X3),k1_relat_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_88,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,k1_xboole_0,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk8_0,X1,k1_xboole_0),esk4_0)
    | ~ r2_hidden(esk1_3(esk8_0,X1,k1_xboole_0),esk6_0)
    | ~ r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_84]),c_0_30]),c_0_31])])])).

cnf(c_0_90,plain,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,X2),X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k9_relat_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_39])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_79])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk4_0)
    | ~ r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_65])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_relset_1(X1,X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_64])).

cnf(c_0_96,plain,
    ( k1_relset_1(k1_xboole_0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_54]),c_0_93])])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_90]),c_0_65])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:12:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.029 s
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 0.12/0.40  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.12/0.40  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.12/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.12/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.12/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.40  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 0.12/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.12/0.40  fof(c_0_14, plain, ![X22, X23, X24]:(((r2_hidden(X22,k1_relat_1(X24))|~r2_hidden(k4_tarski(X22,X23),X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(X23=k1_funct_1(X24,X22)|~r2_hidden(k4_tarski(X22,X23),X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))))&(~r2_hidden(X22,k1_relat_1(X24))|X23!=k1_funct_1(X24,X22)|r2_hidden(k4_tarski(X22,X23),X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.12/0.40  fof(c_0_15, plain, ![X17, X18, X19, X21]:((((r2_hidden(esk1_3(X17,X18,X19),k1_relat_1(X19))|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk1_3(X17,X18,X19),X17),X19)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(r2_hidden(esk1_3(X17,X18,X19),X18)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(~r2_hidden(X21,k1_relat_1(X19))|~r2_hidden(k4_tarski(X21,X17),X19)|~r2_hidden(X21,X18)|r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.12/0.40  fof(c_0_16, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.40  fof(c_0_17, negated_conjecture, ![X50]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))&(~r2_hidden(X50,esk4_0)|~r2_hidden(X50,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X50)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.12/0.40  fof(c_0_18, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.40  fof(c_0_19, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k1_relset_1(X28,X29,X30)=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.40  cnf(c_0_20, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_22, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.40  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_24, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.40  fof(c_0_25, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k7_relset_1(X31,X32,X33,X34)=k9_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.12/0.40  cnf(c_0_26, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.40  fof(c_0_27, plain, ![X42, X43, X44]:((((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))))&((~v1_funct_2(X44,X42,X43)|X44=k1_xboole_0|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X44!=k1_xboole_0|v1_funct_2(X44,X42,X43)|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.12/0.40  cnf(c_0_28, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_29, plain, (k1_funct_1(X1,esk1_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.40  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.12/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_33, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.40  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk7_0)=k1_relset_1(esk4_0,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.12/0.40  cnf(c_0_36, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk4_0)|~r2_hidden(esk1_3(esk8_0,X1,esk7_0),esk6_0)|~r2_hidden(esk8_0,k9_relat_1(esk7_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])])).
% 0.12/0.40  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_23])])).
% 0.12/0.40  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,esk5_0,esk7_0))|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_31])])).
% 0.12/0.40  cnf(c_0_42, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk7_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_37])])).
% 0.12/0.40  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk1_3(esk8_0,esk6_0,esk7_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_31])])).
% 0.12/0.40  cnf(c_0_44, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk7_0),esk4_0)|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.40  fof(c_0_45, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.40  fof(c_0_46, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.40  cnf(c_0_47, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_48, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_40])])).
% 0.12/0.40  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.40  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.40  cnf(c_0_51, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_47])).
% 0.12/0.40  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_23, c_0_48])).
% 0.12/0.40  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_37, c_0_48])).
% 0.12/0.40  cnf(c_0_54, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.40  cnf(c_0_55, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.40  cnf(c_0_56, negated_conjecture, (esk7_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.12/0.40  fof(c_0_57, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|(~r2_hidden(X10,X9)|r2_hidden(X10,X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.40  cnf(c_0_58, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_54])).
% 0.12/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(esk4_0,k1_xboole_0,esk7_0))|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(rw,[status(thm)],[c_0_41, c_0_48])).
% 0.12/0.40  cnf(c_0_60, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_55])).
% 0.12/0.40  cnf(c_0_61, negated_conjecture, (esk7_0=k1_xboole_0|m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 0.12/0.40  cnf(c_0_62, negated_conjecture, (esk7_0=k1_xboole_0|v1_funct_2(esk7_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_56])).
% 0.12/0.40  cnf(c_0_63, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.40  cnf(c_0_64, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_54])).
% 0.12/0.40  cnf(c_0_65, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_24])).
% 0.12/0.40  cnf(c_0_66, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk7_0),k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0))|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_59, c_0_56])).
% 0.12/0.40  cnf(c_0_67, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk7_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.12/0.40  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_54])).
% 0.12/0.40  cnf(c_0_69, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_70, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relset_1(X3,X4,k1_xboole_0))|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_64]), c_0_65])])).
% 0.12/0.40  cnf(c_0_71, negated_conjecture, (esk7_0=k1_xboole_0|~r2_hidden(esk1_3(esk8_0,esk6_0,esk7_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_56])).
% 0.12/0.40  cnf(c_0_72, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_3(X1,X2,esk7_0),k1_xboole_0)|~r2_hidden(X1,k9_relat_1(esk7_0,X2))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.12/0.40  fof(c_0_73, plain, ![X35, X36, X37, X39, X40]:(((r2_hidden(esk2_3(X35,X36,X37),X36)|k1_relset_1(X36,X35,X37)=X36|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35))))&(~r2_hidden(k4_tarski(esk2_3(X35,X36,X37),X39),X37)|k1_relset_1(X36,X35,X37)=X36|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35)))))&(k1_relset_1(X36,X35,X37)!=X36|(~r2_hidden(X40,X36)|r2_hidden(k4_tarski(X40,esk3_4(X35,X36,X37,X40)),X37))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.12/0.40  cnf(c_0_74, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  fof(c_0_75, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.40  cnf(c_0_76, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,k1_xboole_0),X1),X3)|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_21]), c_0_65])])).
% 0.12/0.40  cnf(c_0_77, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(esk1_3(X1,X4,X2),X3)|~r2_hidden(X1,k9_relat_1(X2,X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_21]), c_0_34])).
% 0.12/0.40  cnf(c_0_78, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_relat_1(k1_xboole_0))|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_70, c_0_64])).
% 0.12/0.40  cnf(c_0_79, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_40])])).
% 0.12/0.40  cnf(c_0_80, plain, (k1_relset_1(X2,X1,X3)=X2|~r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X4),X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.40  cnf(c_0_81, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_74])).
% 0.12/0.40  cnf(c_0_82, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.12/0.40  cnf(c_0_83, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|k1_relset_1(X2,X1,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.40  cnf(c_0_84, plain, (k1_funct_1(X1,esk1_3(X2,X3,k1_xboole_0))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_20, c_0_76])).
% 0.12/0.40  cnf(c_0_85, plain, (r2_hidden(X1,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))|~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_65])])).
% 0.12/0.40  cnf(c_0_86, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,esk6_0))), inference(rw,[status(thm)],[c_0_40, c_0_79])).
% 0.12/0.40  cnf(c_0_87, plain, (k1_relset_1(X1,X2,X3)=X1|~v1_funct_1(X3)|~r2_hidden(esk2_3(X2,X1,X3),k1_relat_1(X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.12/0.40  cnf(c_0_88, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,k1_xboole_0,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_68, c_0_83])).
% 0.12/0.40  cnf(c_0_89, negated_conjecture, (~r2_hidden(esk1_3(esk8_0,X1,k1_xboole_0),esk4_0)|~r2_hidden(esk1_3(esk8_0,X1,k1_xboole_0),esk6_0)|~r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_84]), c_0_30]), c_0_31])])])).
% 0.12/0.40  cnf(c_0_90, plain, (r2_hidden(esk1_3(X1,k1_xboole_0,X2),X3)|~v1_relat_1(X2)|~r2_hidden(X1,k9_relat_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_68, c_0_39])).
% 0.12/0.40  cnf(c_0_91, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.12/0.40  cnf(c_0_92, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.12/0.40  cnf(c_0_93, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_30, c_0_79])).
% 0.12/0.40  cnf(c_0_94, negated_conjecture, (~r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk4_0)|~r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_65])])).
% 0.12/0.40  cnf(c_0_95, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_relset_1(X1,X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_91, c_0_64])).
% 0.12/0.40  cnf(c_0_96, plain, (k1_relset_1(k1_xboole_0,X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_54]), c_0_93])])).
% 0.12/0.40  cnf(c_0_97, negated_conjecture, (~r2_hidden(esk8_0,k9_relat_1(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_90]), c_0_65])])).
% 0.12/0.40  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 99
% 0.12/0.40  # Proof object clause steps            : 72
% 0.12/0.40  # Proof object formula steps           : 27
% 0.12/0.40  # Proof object conjectures             : 36
% 0.12/0.40  # Proof object clause conjectures      : 33
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 24
% 0.12/0.40  # Proof object initial formulas used   : 13
% 0.12/0.40  # Proof object generating inferences   : 40
% 0.12/0.40  # Proof object simplifying inferences  : 49
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 13
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 30
% 0.12/0.40  # Removed in clause preprocessing      : 0
% 0.12/0.40  # Initial clauses in saturation        : 30
% 0.12/0.40  # Processed clauses                    : 340
% 0.12/0.40  # ...of these trivial                  : 2
% 0.12/0.40  # ...subsumed                          : 164
% 0.12/0.40  # ...remaining for further processing  : 174
% 0.12/0.40  # Other redundant clauses eliminated   : 27
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 5
% 0.12/0.40  # Backward-rewritten                   : 63
% 0.12/0.40  # Generated clauses                    : 712
% 0.12/0.40  # ...of the previous two non-trivial   : 692
% 0.12/0.40  # Contextual simplify-reflections      : 8
% 0.12/0.40  # Paramodulations                      : 686
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 27
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 101
% 0.12/0.40  #    Positive orientable unit clauses  : 13
% 0.12/0.40  #    Positive unorientable unit clauses: 2
% 0.12/0.40  #    Negative unit clauses             : 2
% 0.12/0.40  #    Non-unit-clauses                  : 84
% 0.12/0.40  # Current number of unprocessed clauses: 314
% 0.12/0.40  # ...number of literals in the above   : 1504
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 68
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 2375
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 1026
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 165
% 0.12/0.40  # Unit Clause-clause subsumption calls : 46
% 0.12/0.40  # Rewrite failures with RHS unbound    : 64
% 0.12/0.40  # BW rewrite match attempts            : 16
% 0.12/0.40  # BW rewrite match successes           : 8
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 16028
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.056 s
% 0.12/0.40  # System time              : 0.004 s
% 0.12/0.40  # Total time               : 0.059 s
% 0.12/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
