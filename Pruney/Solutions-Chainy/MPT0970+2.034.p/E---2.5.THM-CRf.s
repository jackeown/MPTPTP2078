%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:31 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 645 expanded)
%              Number of clauses        :   53 ( 266 expanded)
%              Number of leaves         :   13 ( 156 expanded)
%              Depth                    :   12
%              Number of atoms          :  287 (2820 expanded)
%              Number of equality atoms :   99 ( 760 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

fof(c_0_14,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k1_relset_1(X38,X39,X40) = k1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,plain,(
    ! [X44,X45,X46] :
      ( ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X46 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X46 != k1_xboole_0
        | v1_funct_2(X46,X44,X45)
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ r2_hidden(X16,X15)
      | r2_hidden(X16,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_17,negated_conjecture,(
    ! [X50] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & ( r2_hidden(esk9_1(X50),esk6_0)
        | ~ r2_hidden(X50,esk7_0) )
      & ( X50 = k1_funct_1(esk8_0,esk9_1(X50))
        | ~ r2_hidden(X50,esk7_0) )
      & k2_relset_1(esk6_0,esk7_0,esk8_0) != esk7_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

cnf(c_0_18,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r2_hidden(X10,X12)
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) )
      & ( r2_hidden(X11,X13)
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) )
      & ( ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X11,X13)
        | r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_24,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | ~ r1_tarski(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_28,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_31,plain,(
    ! [X17,X18,X19,X21] :
      ( ( r2_hidden(esk2_3(X17,X18,X19),k1_relat_1(X19))
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk2_3(X17,X18,X19),X17),X19)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X18)
        | ~ r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(X21,k1_relat_1(X19))
        | ~ r2_hidden(k4_tarski(X21,X17),X19)
        | ~ r2_hidden(X21,X18)
        | r2_hidden(X17,k9_relat_1(X19,X18))
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk8_0)
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_22])])).

cnf(c_0_34,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_22])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ( ~ r2_hidden(esk1_2(X6,X7),X6)
        | ~ r2_hidden(esk1_2(X6,X7),X7)
        | X6 = X7 )
      & ( r2_hidden(esk1_2(X6,X7),X6)
        | r2_hidden(esk1_2(X6,X7),X7)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_41,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_42,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k9_relat_1(X22,k1_relat_1(X22)) = k2_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_48,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k2_relset_1(X41,X42,X43) = k2_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_49,plain,(
    ! [X23,X24,X25,X27,X28,X29,X31] :
      ( ( r2_hidden(esk3_3(X23,X24,X25),k1_relat_1(X23))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X25 = k1_funct_1(X23,esk3_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X28,k1_relat_1(X23))
        | X27 != k1_funct_1(X23,X28)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(esk4_2(X23,X29),X29)
        | ~ r2_hidden(X31,k1_relat_1(X23))
        | esk4_2(X23,X29) != k1_funct_1(X23,X31)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk5_2(X23,X29),k1_relat_1(X23))
        | r2_hidden(esk4_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( esk4_2(X23,X29) = k1_funct_1(X23,esk5_2(X23,X29))
        | r2_hidden(esk4_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_50,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_41])).

cnf(c_0_51,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39])]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = X2
    | r2_hidden(esk1_2(k9_relat_1(esk8_0,X1),X2),esk7_0)
    | r2_hidden(esk1_2(k9_relat_1(esk8_0,X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k2_relset_1(esk6_0,esk7_0,esk8_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( X1 = k1_funct_1(esk8_0,esk9_1(X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk9_1(X1),esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk8_0)
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_22])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_39])])).

cnf(c_0_62,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_39])])).

cnf(c_0_63,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = esk7_0
    | r2_hidden(esk1_2(k9_relat_1(esk8_0,X1),esk7_0),esk7_0) ),
    inference(ef,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k2_relat_1(esk8_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk8_0)
    | ~ r2_hidden(esk9_1(X1),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])]),c_0_39])])).

cnf(c_0_67,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk9_1(X1),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( X1 = k2_relat_1(esk8_0)
    | r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),esk7_0)
    | r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_51]),c_0_39])]),c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_relat_1(esk8_0)),esk7_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_68]),c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1)
    | X1 != k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_relat_1(k1_xboole_0)),esk7_0)
    | esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_78]),c_0_78])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.029 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 0.19/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.44  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.44  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.44  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.44  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.44  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.44  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.44  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.44  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.44  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.44  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.19/0.44  fof(c_0_14, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k1_relset_1(X38,X39,X40)=k1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.44  fof(c_0_15, plain, ![X44, X45, X46]:((((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&((~v1_funct_2(X46,X44,X45)|X46=k1_xboole_0|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X46!=k1_xboole_0|v1_funct_2(X46,X44,X45)|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.44  fof(c_0_16, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|(~r2_hidden(X16,X15)|r2_hidden(X16,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.44  fof(c_0_17, negated_conjecture, ![X50]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(((r2_hidden(esk9_1(X50),esk6_0)|~r2_hidden(X50,esk7_0))&(X50=k1_funct_1(esk8_0,esk9_1(X50))|~r2_hidden(X50,esk7_0)))&k2_relset_1(esk6_0,esk7_0,esk8_0)!=esk7_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).
% 0.19/0.44  cnf(c_0_18, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_19, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  fof(c_0_20, plain, ![X10, X11, X12, X13]:(((r2_hidden(X10,X12)|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)))&(r2_hidden(X11,X13)|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13))))&(~r2_hidden(X10,X12)|~r2_hidden(X11,X13)|r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(X12,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.44  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  fof(c_0_23, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.44  cnf(c_0_24, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.44  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_26, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  fof(c_0_27, plain, ![X33, X34]:(~r2_hidden(X33,X34)|~r1_tarski(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.44  fof(c_0_28, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.44  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk6_0,esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.44  fof(c_0_31, plain, ![X17, X18, X19, X21]:((((r2_hidden(esk2_3(X17,X18,X19),k1_relat_1(X19))|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk2_3(X17,X18,X19),X17),X19)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(r2_hidden(esk2_3(X17,X18,X19),X18)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(~r2_hidden(X21,k1_relat_1(X19))|~r2_hidden(k4_tarski(X21,X17),X19)|~r2_hidden(X21,X18)|r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.44  cnf(c_0_32, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_33, negated_conjecture, (esk6_0=k1_relat_1(esk8_0)|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_22])])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_25]), c_0_22])])).
% 0.19/0.44  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.44  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(k4_tarski(X2,X1),esk8_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.44  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.19/0.44  fof(c_0_40, plain, ![X6, X7]:((~r2_hidden(esk1_2(X6,X7),X6)|~r2_hidden(esk1_2(X6,X7),X7)|X6=X7)&(r2_hidden(esk1_2(X6,X7),X6)|r2_hidden(esk1_2(X6,X7),X7)|X6=X7)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.44  cnf(c_0_41, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  fof(c_0_42, plain, ![X22]:(~v1_relat_1(X22)|k9_relat_1(X22,k1_relat_1(X22))=k2_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.44  cnf(c_0_43, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.44  cnf(c_0_45, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.44  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.44  fof(c_0_48, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k2_relset_1(X41,X42,X43)=k2_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.44  fof(c_0_49, plain, ![X23, X24, X25, X27, X28, X29, X31]:((((r2_hidden(esk3_3(X23,X24,X25),k1_relat_1(X23))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X25=k1_funct_1(X23,esk3_3(X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X28,k1_relat_1(X23))|X27!=k1_funct_1(X23,X28)|r2_hidden(X27,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&((~r2_hidden(esk4_2(X23,X29),X29)|(~r2_hidden(X31,k1_relat_1(X23))|esk4_2(X23,X29)!=k1_funct_1(X23,X31))|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&((r2_hidden(esk5_2(X23,X29),k1_relat_1(X23))|r2_hidden(esk4_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(esk4_2(X23,X29)=k1_funct_1(X23,esk5_2(X23,X29))|r2_hidden(esk4_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.44  cnf(c_0_50, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_18, c_0_41])).
% 0.19/0.44  cnf(c_0_51, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0!=k1_xboole_0|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39])]), c_0_45])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (k9_relat_1(esk8_0,X1)=X2|r2_hidden(esk1_2(k9_relat_1(esk8_0,X1),X2),esk7_0)|r2_hidden(esk1_2(k9_relat_1(esk8_0,X1),X2),X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (k2_relset_1(esk6_0,esk7_0,esk8_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_55, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.44  cnf(c_0_56, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.44  cnf(c_0_57, negated_conjecture, (X1=k1_funct_1(esk8_0,esk9_1(X1))|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_58, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_59, negated_conjecture, (r2_hidden(esk9_1(X1),esk6_0)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (esk6_0=k1_relat_1(esk8_0)|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_25]), c_0_22])])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_39])])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0!=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_51]), c_0_39])])).
% 0.19/0.44  cnf(c_0_63, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (k9_relat_1(esk8_0,X1)=esk7_0|r2_hidden(esk1_2(k9_relat_1(esk8_0,X1),esk7_0),esk7_0)), inference(ef,[status(thm)],[c_0_53])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (k2_relat_1(esk8_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_22])])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,X2)|X2!=k2_relat_1(esk8_0)|~r2_hidden(esk9_1(X1),k1_relat_1(esk8_0))|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])]), c_0_39])])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk9_1(X1),k1_relat_1(esk8_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (X1=k2_relat_1(esk8_0)|r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),esk7_0)|r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),X1)), inference(spm,[status(thm)],[c_0_61, c_0_47])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.44  cnf(c_0_70, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.44  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_51]), c_0_39])]), c_0_65])).
% 0.19/0.44  cnf(c_0_72, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(X1,X2)|X2!=k2_relat_1(esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_relat_1(esk8_0)),esk7_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_68]), c_0_65])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_69])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (~r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_65])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1)|X1!=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_72, c_0_71])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_relat_1(k1_xboole_0)),esk7_0)|esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.44  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_78]), c_0_78])]), c_0_45]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 80
% 0.19/0.44  # Proof object clause steps            : 53
% 0.19/0.44  # Proof object formula steps           : 27
% 0.19/0.44  # Proof object conjectures             : 36
% 0.19/0.44  # Proof object clause conjectures      : 33
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 22
% 0.19/0.44  # Proof object initial formulas used   : 13
% 0.19/0.44  # Proof object generating inferences   : 30
% 0.19/0.44  # Proof object simplifying inferences  : 32
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 13
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 34
% 0.19/0.44  # Removed in clause preprocessing      : 0
% 0.19/0.44  # Initial clauses in saturation        : 34
% 0.19/0.44  # Processed clauses                    : 596
% 0.19/0.44  # ...of these trivial                  : 12
% 0.19/0.44  # ...subsumed                          : 331
% 0.19/0.44  # ...remaining for further processing  : 253
% 0.19/0.44  # Other redundant clauses eliminated   : 3
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 19
% 0.19/0.44  # Backward-rewritten                   : 81
% 0.19/0.44  # Generated clauses                    : 2107
% 0.19/0.44  # ...of the previous two non-trivial   : 2024
% 0.19/0.44  # Contextual simplify-reflections      : 9
% 0.19/0.44  # Paramodulations                      : 2092
% 0.19/0.44  # Factorizations                       : 10
% 0.19/0.44  # Equation resolutions                 : 5
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 119
% 0.19/0.44  #    Positive orientable unit clauses  : 4
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 114
% 0.19/0.44  # Current number of unprocessed clauses: 1480
% 0.19/0.44  # ...number of literals in the above   : 6749
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 134
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 4960
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 1828
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 265
% 0.19/0.44  # Unit Clause-clause subsumption calls : 56
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 1
% 0.19/0.44  # BW rewrite match successes           : 1
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 31295
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.086 s
% 0.19/0.44  # System time              : 0.006 s
% 0.19/0.44  # Total time               : 0.092 s
% 0.19/0.44  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
