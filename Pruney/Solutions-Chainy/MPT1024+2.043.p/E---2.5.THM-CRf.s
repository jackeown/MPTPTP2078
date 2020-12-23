%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:32 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 216 expanded)
%              Number of clauses        :   46 (  87 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  275 (1124 expanded)
%              Number of equality atoms :   88 ( 254 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(c_0_10,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( r2_hidden(esk3_4(X22,X23,X24,X25),k1_relat_1(X22))
        | ~ r2_hidden(X25,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk3_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X25 = k1_funct_1(X22,esk3_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X28,k1_relat_1(X22))
        | ~ r2_hidden(X28,X23)
        | X27 != k1_funct_1(X22,X28)
        | r2_hidden(X27,X24)
        | X24 != k9_relat_1(X22,X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk4_3(X22,X29,X30),X30)
        | ~ r2_hidden(X32,k1_relat_1(X22))
        | ~ r2_hidden(X32,X29)
        | esk4_3(X22,X29,X30) != k1_funct_1(X22,X32)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk5_3(X22,X29,X30),k1_relat_1(X22))
        | r2_hidden(esk4_3(X22,X29,X30),X30)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk5_3(X22,X29,X30),X29)
        | r2_hidden(esk4_3(X22,X29,X30),X30)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk4_3(X22,X29,X30) = k1_funct_1(X22,esk5_3(X22,X29,X30))
        | r2_hidden(esk4_3(X22,X29,X30),X30)
        | X30 = k9_relat_1(X22,X29)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_12,negated_conjecture,(
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

cnf(c_0_13,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,negated_conjecture,(
    ! [X49] :
      ( v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))
      & ( ~ r2_hidden(X49,esk6_0)
        | ~ r2_hidden(X49,esk8_0)
        | esk10_0 != k1_funct_1(esk9_0,X49) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_17,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_18,plain,
    ( X1 = k9_relat_1(X2,X3)
    | r2_hidden(esk4_3(X2,X3,X1),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = k9_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k9_relat_1(esk9_0,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_26,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_27,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_28,plain,(
    ! [X41,X42,X43] :
      ( ( ~ v1_funct_2(X43,X41,X42)
        | X41 = k1_relset_1(X41,X42,X43)
        | X42 = k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X41 != k1_relset_1(X41,X42,X43)
        | v1_funct_2(X43,X41,X42)
        | X42 = k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( ~ v1_funct_2(X43,X41,X42)
        | X41 = k1_relset_1(X41,X42,X43)
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X41 != k1_relset_1(X41,X42,X43)
        | v1_funct_2(X43,X41,X42)
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( ~ v1_funct_2(X43,X41,X42)
        | X43 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X43 != k1_xboole_0
        | v1_funct_2(X43,X41,X42)
        | X41 = k1_xboole_0
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_29,plain,(
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

fof(c_0_30,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k7_relset_1(X37,X38,X39,X40) = k9_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( k9_relat_1(esk9_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( X1 != k9_relat_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( k9_relat_1(esk9_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_45,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20])])).

cnf(c_0_47,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23]),c_0_24]),c_0_26])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_20])])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_20])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24])])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk8_0)
    | esk10_0 != k1_funct_1(esk9_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,plain,
    ( X1 = k1_funct_1(X2,esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0)
    | esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( X1 != k9_relat_1(esk9_0,X2)
    | esk10_0 != X3
    | ~ r2_hidden(esk3_4(esk9_0,X2,X1,X3),esk6_0)
    | ~ r2_hidden(esk3_4(esk9_0,X2,X1,X3),esk8_0)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_23])]),c_0_24])])).

cnf(c_0_59,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk9_0) ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( X1 != k9_relat_1(esk9_0,X2)
    | esk10_0 != X3
    | ~ r2_hidden(esk3_4(esk9_0,X2,X1,X3),k1_relat_1(esk9_0))
    | ~ r2_hidden(esk3_4(esk9_0,X2,X1,X3),esk8_0)
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( X1 != k9_relat_1(esk9_0,esk8_0)
    | esk10_0 != X2
    | ~ r2_hidden(esk3_4(esk9_0,esk8_0,X1,X2),k1_relat_1(esk9_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_31]),c_0_23]),c_0_24])])).

cnf(c_0_62,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_63,negated_conjecture,
    ( X1 != k9_relat_1(esk9_0,esk8_0)
    | esk10_0 != X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_23]),c_0_24])])).

cnf(c_0_64,negated_conjecture,
    ( esk10_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,esk8_0)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_64,c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.21/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.39  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.21/0.39  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 0.21/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.21/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.39  fof(c_0_10, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.39  fof(c_0_11, plain, ![X22, X23, X24, X25, X27, X28, X29, X30, X32]:(((((r2_hidden(esk3_4(X22,X23,X24,X25),k1_relat_1(X22))|~r2_hidden(X25,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(esk3_4(X22,X23,X24,X25),X23)|~r2_hidden(X25,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(X25=k1_funct_1(X22,esk3_4(X22,X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X28,k1_relat_1(X22))|~r2_hidden(X28,X23)|X27!=k1_funct_1(X22,X28)|r2_hidden(X27,X24)|X24!=k9_relat_1(X22,X23)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&((~r2_hidden(esk4_3(X22,X29,X30),X30)|(~r2_hidden(X32,k1_relat_1(X22))|~r2_hidden(X32,X29)|esk4_3(X22,X29,X30)!=k1_funct_1(X22,X32))|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(((r2_hidden(esk5_3(X22,X29,X30),k1_relat_1(X22))|r2_hidden(esk4_3(X22,X29,X30),X30)|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(esk5_3(X22,X29,X30),X29)|r2_hidden(esk4_3(X22,X29,X30),X30)|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(esk4_3(X22,X29,X30)=k1_funct_1(X22,esk5_3(X22,X29,X30))|r2_hidden(esk4_3(X22,X29,X30),X30)|X30=k9_relat_1(X22,X29)|(~v1_relat_1(X22)|~v1_funct_1(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.21/0.39  cnf(c_0_13, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_14, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  fof(c_0_15, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.39  fof(c_0_16, negated_conjecture, ![X49]:(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))&(~r2_hidden(X49,esk6_0)|~r2_hidden(X49,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X49)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.21/0.39  fof(c_0_17, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.39  cnf(c_0_18, plain, (X1=k9_relat_1(X2,X3)|r2_hidden(esk4_3(X2,X3,X1),X1)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  cnf(c_0_19, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_21, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_22, plain, (X1=k9_relat_1(X2,X3)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_xboole_0(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (X1=k9_relat_1(esk9_0,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.21/0.39  cnf(c_0_26, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.39  fof(c_0_27, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k1_relset_1(X34,X35,X36)=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.39  fof(c_0_28, plain, ![X41, X42, X43]:((((~v1_funct_2(X43,X41,X42)|X41=k1_relset_1(X41,X42,X43)|X42=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(X41!=k1_relset_1(X41,X42,X43)|v1_funct_2(X43,X41,X42)|X42=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&((~v1_funct_2(X43,X41,X42)|X41=k1_relset_1(X41,X42,X43)|X41!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(X41!=k1_relset_1(X41,X42,X43)|v1_funct_2(X43,X41,X42)|X41!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))))&((~v1_funct_2(X43,X41,X42)|X43=k1_xboole_0|X41=k1_xboole_0|X42!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(X43!=k1_xboole_0|v1_funct_2(X43,X41,X42)|X41=k1_xboole_0|X42!=k1_xboole_0|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.39  fof(c_0_29, plain, ![X17, X18, X19, X21]:((((r2_hidden(esk2_3(X17,X18,X19),k1_relat_1(X19))|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk2_3(X17,X18,X19),X17),X19)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(r2_hidden(esk2_3(X17,X18,X19),X18)|~r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19)))&(~r2_hidden(X21,k1_relat_1(X19))|~r2_hidden(k4_tarski(X21,X17),X19)|~r2_hidden(X21,X18)|r2_hidden(X17,k9_relat_1(X19,X18))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.21/0.39  fof(c_0_30, plain, ![X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k7_relset_1(X37,X38,X39,X40)=k9_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.39  cnf(c_0_31, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (k9_relat_1(esk9_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.39  cnf(c_0_33, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_34, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_35, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(esk10_0,k7_relset_1(esk6_0,esk7_0,esk9_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_38, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.39  cnf(c_0_39, plain, (X1!=k9_relat_1(X2,X3)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X4,X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_13, c_0_31])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (k9_relat_1(esk9_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.21/0.39  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_43, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.39  cnf(c_0_44, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 0.21/0.39  cnf(c_0_45, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_13, c_0_36])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(esk10_0,k9_relat_1(esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_20])])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_23]), c_0_24]), c_0_26])])).
% 0.21/0.39  cnf(c_0_48, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, (esk9_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_20])])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_42]), c_0_20])])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_42]), c_0_20])])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24])])).
% 0.21/0.39  cnf(c_0_53, negated_conjecture, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk8_0)|esk10_0!=k1_funct_1(esk9_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_55, plain, (X1=k1_funct_1(X2,esk3_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)|esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (esk9_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (X1!=k9_relat_1(esk9_0,X2)|esk10_0!=X3|~r2_hidden(esk3_4(esk9_0,X2,X1,X3),esk6_0)|~r2_hidden(esk3_4(esk9_0,X2,X1,X3),esk8_0)|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_23])]), c_0_24])])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (esk6_0=k1_relat_1(esk9_0)), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (X1!=k9_relat_1(esk9_0,X2)|esk10_0!=X3|~r2_hidden(esk3_4(esk9_0,X2,X1,X3),k1_relat_1(esk9_0))|~r2_hidden(esk3_4(esk9_0,X2,X1,X3),esk8_0)|~r2_hidden(X3,X1)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.39  cnf(c_0_61, negated_conjecture, (X1!=k9_relat_1(esk9_0,esk8_0)|esk10_0!=X2|~r2_hidden(esk3_4(esk9_0,esk8_0,X1,X2),k1_relat_1(esk9_0))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_31]), c_0_23]), c_0_24])])).
% 0.21/0.39  cnf(c_0_62, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (X1!=k9_relat_1(esk9_0,esk8_0)|esk10_0!=X2|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_23]), c_0_24])])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (esk10_0!=X1|~r2_hidden(X1,k9_relat_1(esk9_0,esk8_0))), inference(er,[status(thm)],[c_0_63])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_64, c_0_46]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 66
% 0.21/0.39  # Proof object clause steps            : 46
% 0.21/0.39  # Proof object formula steps           : 20
% 0.21/0.39  # Proof object conjectures             : 28
% 0.21/0.39  # Proof object clause conjectures      : 25
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 20
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 24
% 0.21/0.39  # Proof object simplifying inferences  : 31
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 11
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 34
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 34
% 0.21/0.39  # Processed clauses                    : 306
% 0.21/0.39  # ...of these trivial                  : 4
% 0.21/0.39  # ...subsumed                          : 111
% 0.21/0.39  # ...remaining for further processing  : 191
% 0.21/0.39  # Other redundant clauses eliminated   : 1
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 1
% 0.21/0.39  # Backward-rewritten                   : 21
% 0.21/0.39  # Generated clauses                    : 523
% 0.21/0.39  # ...of the previous two non-trivial   : 470
% 0.21/0.39  # Contextual simplify-reflections      : 3
% 0.21/0.39  # Paramodulations                      : 505
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 12
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 129
% 0.21/0.39  #    Positive orientable unit clauses  : 12
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 14
% 0.21/0.39  #    Non-unit-clauses                  : 103
% 0.21/0.39  # Current number of unprocessed clauses: 209
% 0.21/0.39  # ...number of literals in the above   : 1075
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 62
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 938
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 409
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 49
% 0.21/0.39  # Unit Clause-clause subsumption calls : 57
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 2
% 0.21/0.39  # BW rewrite match successes           : 2
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 9568
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.048 s
% 0.21/0.39  # System time              : 0.002 s
% 0.21/0.39  # Total time               : 0.050 s
% 0.21/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
