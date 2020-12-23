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
% DateTime   : Thu Dec  3 11:06:29 EST 2020

% Result     : Theorem 20.40s
% Output     : CNFRefutation 20.40s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 212 expanded)
%              Number of clauses        :   39 (  88 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 917 expanded)
%              Number of equality atoms :   16 (  86 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(t52_relset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X19,X20,X21,X23] :
      ( ( r2_hidden(esk2_3(X19,X20,X21),k1_relat_1(X21))
        | ~ r2_hidden(X19,k9_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk2_3(X19,X20,X21),X19),X21)
        | ~ r2_hidden(X19,k9_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | ~ r2_hidden(X19,k9_relat_1(X21,X20))
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X23,k1_relat_1(X21))
        | ~ r2_hidden(k4_tarski(X23,X19),X21)
        | ~ r2_hidden(X23,X20)
        | r2_hidden(X19,k9_relat_1(X21,X20))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_14,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | m1_subset_1(k7_relset_1(X36,X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k7_relset_1(X40,X41,X42,X43) = k9_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( ( r2_hidden(X24,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( X25 = k1_funct_1(X26,X24)
        | ~ r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X24,k1_relat_1(X26))
        | X25 != k1_funct_1(X26,X24)
        | r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_22,plain,(
    ! [X44,X45,X46,X47,X48,X50] :
      ( ( m1_subset_1(esk3_5(X44,X45,X46,X47,X48),X46)
        | ~ r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))
        | ~ m1_subset_1(X48,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45)
        | v1_xboole_0(X44) )
      & ( r2_hidden(k4_tarski(esk3_5(X44,X45,X46,X47,X48),X48),X47)
        | ~ r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))
        | ~ m1_subset_1(X48,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45)
        | v1_xboole_0(X44) )
      & ( r2_hidden(esk3_5(X44,X45,X46,X47,X48),X45)
        | ~ r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))
        | ~ m1_subset_1(X48,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45)
        | v1_xboole_0(X44) )
      & ( ~ m1_subset_1(X50,X46)
        | ~ r2_hidden(k4_tarski(X50,X48),X47)
        | ~ r2_hidden(X50,X45)
        | r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))
        | ~ m1_subset_1(X48,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45)
        | v1_xboole_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,negated_conjecture,(
    ! [X56] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))
      & ( ~ r2_hidden(X56,esk4_0)
        | ~ r2_hidden(X56,esk6_0)
        | esk8_0 != k1_funct_1(esk7_0,X56) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).

cnf(c_0_29,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | esk8_0 != k1_funct_1(esk7_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k1_funct_1(X1,esk3_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_27]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_39,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk8_0 != X3
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk4_0)
    | ~ r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk6_0)
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,esk7_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_36]),c_0_37])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk8_0,k7_relset_1(X1,X2,esk7_0,esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_39]),c_0_37])])).

fof(c_0_46,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_xboole_0(X33)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33)))
      | v1_xboole_0(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk8_0 != X3
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(esk3_5(X1,esk6_0,X2,esk7_0,X3),esk4_0)
    | ~ r2_hidden(X3,k7_relset_1(X2,X1,esk7_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_31])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31]),c_0_32])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_26])).

fof(c_0_51,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_xboole_0(X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | v1_xboole_0(X1)
    | esk8_0 != X2
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r2_hidden(X2,k7_relset_1(esk4_0,X1,esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_37])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_36]),c_0_37])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_37])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:23:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 20.40/20.57  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 20.40/20.57  # and selection function SelectMaxLComplexAvoidPosPred.
% 20.40/20.57  #
% 20.40/20.57  # Preprocessing time       : 0.042 s
% 20.40/20.57  # Presaturation interreduction done
% 20.40/20.57  
% 20.40/20.57  # Proof found!
% 20.40/20.57  # SZS status Theorem
% 20.40/20.57  # SZS output start CNFRefutation
% 20.40/20.57  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 20.40/20.57  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 20.40/20.57  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 20.40/20.57  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 20.40/20.57  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 20.40/20.57  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 20.40/20.57  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 20.40/20.57  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 20.40/20.57  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 20.40/20.57  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 20.40/20.57  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 20.40/20.57  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 20.40/20.57  fof(c_0_12, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 20.40/20.57  fof(c_0_13, plain, ![X19, X20, X21, X23]:((((r2_hidden(esk2_3(X19,X20,X21),k1_relat_1(X21))|~r2_hidden(X19,k9_relat_1(X21,X20))|~v1_relat_1(X21))&(r2_hidden(k4_tarski(esk2_3(X19,X20,X21),X19),X21)|~r2_hidden(X19,k9_relat_1(X21,X20))|~v1_relat_1(X21)))&(r2_hidden(esk2_3(X19,X20,X21),X20)|~r2_hidden(X19,k9_relat_1(X21,X20))|~v1_relat_1(X21)))&(~r2_hidden(X23,k1_relat_1(X21))|~r2_hidden(k4_tarski(X23,X19),X21)|~r2_hidden(X23,X20)|r2_hidden(X19,k9_relat_1(X21,X20))|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 20.40/20.57  fof(c_0_14, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 20.40/20.57  fof(c_0_15, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|m1_subset_1(k7_relset_1(X36,X37,X38,X39),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 20.40/20.57  cnf(c_0_16, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 20.40/20.57  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 20.40/20.57  fof(c_0_18, plain, ![X40, X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k7_relset_1(X40,X41,X42,X43)=k9_relat_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 20.40/20.57  fof(c_0_19, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 20.40/20.57  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 20.40/20.57  fof(c_0_21, plain, ![X24, X25, X26]:(((r2_hidden(X24,k1_relat_1(X26))|~r2_hidden(k4_tarski(X24,X25),X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(X25=k1_funct_1(X26,X24)|~r2_hidden(k4_tarski(X24,X25),X26)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&(~r2_hidden(X24,k1_relat_1(X26))|X25!=k1_funct_1(X26,X24)|r2_hidden(k4_tarski(X24,X25),X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 20.40/20.57  fof(c_0_22, plain, ![X44, X45, X46, X47, X48, X50]:((((m1_subset_1(esk3_5(X44,X45,X46,X47,X48),X46)|~r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44))&(r2_hidden(k4_tarski(esk3_5(X44,X45,X46,X47,X48),X48),X47)|~r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44)))&(r2_hidden(esk3_5(X44,X45,X46,X47,X48),X45)|~r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44)))&(~m1_subset_1(X50,X46)|~r2_hidden(k4_tarski(X50,X48),X47)|~r2_hidden(X50,X45)|r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 20.40/20.57  cnf(c_0_23, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.40/20.57  cnf(c_0_24, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 20.40/20.57  cnf(c_0_25, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 20.40/20.57  cnf(c_0_26, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 20.40/20.57  cnf(c_0_27, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 20.40/20.57  fof(c_0_28, negated_conjecture, ![X56]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))&(~r2_hidden(X56,esk4_0)|~r2_hidden(X56,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X56)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])])).
% 20.40/20.57  cnf(c_0_29, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 20.40/20.57  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.40/20.57  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 20.40/20.57  cnf(c_0_32, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 20.40/20.57  cnf(c_0_33, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 20.40/20.57  cnf(c_0_34, plain, (k1_funct_1(X1,esk3_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_27]), c_0_32])).
% 20.40/20.57  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 20.40/20.57  cnf(c_0_36, negated_conjecture, (r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 20.40/20.57  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 20.40/20.57  fof(c_0_38, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 20.40/20.57  cnf(c_0_39, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 20.40/20.57  cnf(c_0_40, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk8_0!=X3|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk4_0)|~r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk6_0)|~r2_hidden(X3,k7_relset_1(X1,X2,esk7_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 20.40/20.57  cnf(c_0_41, plain, (r2_hidden(esk3_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.40/20.57  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_36]), c_0_37])])).
% 20.40/20.57  cnf(c_0_43, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 20.40/20.57  cnf(c_0_44, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.40/20.57  cnf(c_0_45, negated_conjecture, (r2_hidden(esk8_0,k7_relset_1(X1,X2,esk7_0,esk6_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_39]), c_0_37])])).
% 20.40/20.57  fof(c_0_46, plain, ![X33, X34, X35]:(~v1_xboole_0(X33)|(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33)))|v1_xboole_0(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 20.40/20.57  cnf(c_0_47, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk8_0!=X3|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r2_hidden(esk3_5(X1,esk6_0,X2,esk7_0,X3),esk4_0)|~r2_hidden(X3,k7_relset_1(X2,X1,esk7_0,esk6_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_31])).
% 20.40/20.57  cnf(c_0_48, plain, (r2_hidden(esk3_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X1)|v1_xboole_0(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_31]), c_0_32])).
% 20.40/20.57  cnf(c_0_49, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 20.40/20.57  cnf(c_0_50, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_26])).
% 20.40/20.57  fof(c_0_51, plain, ![X30, X31, X32]:(~v1_xboole_0(X30)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 20.40/20.57  cnf(c_0_52, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 20.40/20.57  cnf(c_0_53, negated_conjecture, (v1_xboole_0(esk4_0)|v1_xboole_0(X1)|esk8_0!=X2|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r2_hidden(X2,k7_relset_1(esk4_0,X1,esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 20.40/20.57  cnf(c_0_54, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_16, c_0_49])).
% 20.40/20.57  cnf(c_0_55, negated_conjecture, (r2_hidden(esk8_0,k9_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_37])).
% 20.40/20.57  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_37])).
% 20.40/20.57  cnf(c_0_57, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 20.40/20.57  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_37])).
% 20.40/20.57  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk5_0)|v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_36]), c_0_37])])).
% 20.40/20.57  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 20.40/20.57  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_37])).
% 20.40/20.57  cnf(c_0_62, negated_conjecture, (v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 20.40/20.57  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])]), c_0_60]), ['proof']).
% 20.40/20.57  # SZS output end CNFRefutation
% 20.40/20.57  # Proof object total steps             : 64
% 20.40/20.57  # Proof object clause steps            : 39
% 20.40/20.57  # Proof object formula steps           : 25
% 20.40/20.57  # Proof object conjectures             : 21
% 20.40/20.57  # Proof object clause conjectures      : 18
% 20.40/20.57  # Proof object formula conjectures     : 3
% 20.40/20.57  # Proof object initial clauses used    : 18
% 20.40/20.57  # Proof object initial formulas used   : 12
% 20.40/20.57  # Proof object generating inferences   : 20
% 20.40/20.57  # Proof object simplifying inferences  : 22
% 20.40/20.57  # Training examples: 0 positive, 0 negative
% 20.40/20.57  # Parsed axioms                        : 14
% 20.40/20.57  # Removed by relevancy pruning/SinE    : 0
% 20.40/20.57  # Initial clauses                      : 27
% 20.40/20.57  # Removed in clause preprocessing      : 0
% 20.40/20.57  # Initial clauses in saturation        : 27
% 20.40/20.57  # Processed clauses                    : 54508
% 20.40/20.57  # ...of these trivial                  : 22
% 20.40/20.57  # ...subsumed                          : 42836
% 20.40/20.57  # ...remaining for further processing  : 11650
% 20.40/20.57  # Other redundant clauses eliminated   : 6
% 20.40/20.57  # Clauses deleted for lack of memory   : 0
% 20.40/20.57  # Backward-subsumed                    : 1503
% 20.40/20.57  # Backward-rewritten                   : 158
% 20.40/20.57  # Generated clauses                    : 774880
% 20.40/20.57  # ...of the previous two non-trivial   : 766193
% 20.40/20.57  # Contextual simplify-reflections      : 1545
% 20.40/20.57  # Paramodulations                      : 774871
% 20.40/20.57  # Factorizations                       : 0
% 20.40/20.57  # Equation resolutions                 : 8
% 20.40/20.57  # Propositional unsat checks           : 0
% 20.40/20.57  #    Propositional check models        : 0
% 20.40/20.57  #    Propositional check unsatisfiable : 0
% 20.40/20.57  #    Propositional clauses             : 0
% 20.40/20.57  #    Propositional clauses after purity: 0
% 20.40/20.57  #    Propositional unsat core size     : 0
% 20.40/20.57  #    Propositional preprocessing time  : 0.000
% 20.40/20.57  #    Propositional encoding time       : 0.000
% 20.40/20.57  #    Propositional solver time         : 0.000
% 20.40/20.57  #    Success case prop preproc time    : 0.000
% 20.40/20.57  #    Success case prop encoding time   : 0.000
% 20.40/20.57  #    Success case prop solver time     : 0.000
% 20.40/20.57  # Current number of processed clauses  : 9961
% 20.40/20.57  #    Positive orientable unit clauses  : 25
% 20.40/20.57  #    Positive unorientable unit clauses: 0
% 20.40/20.57  #    Negative unit clauses             : 7
% 20.40/20.57  #    Non-unit-clauses                  : 9929
% 20.40/20.57  # Current number of unprocessed clauses: 709387
% 20.40/20.57  # ...number of literals in the above   : 5357927
% 20.40/20.57  # Current number of archived formulas  : 0
% 20.40/20.57  # Current number of archived clauses   : 1689
% 20.40/20.57  # Clause-clause subsumption calls (NU) : 26203591
% 20.40/20.57  # Rec. Clause-clause subsumption calls : 1051418
% 20.40/20.57  # Non-unit clause-clause subsumptions  : 38540
% 20.40/20.57  # Unit Clause-clause subsumption calls : 11293
% 20.40/20.57  # Rewrite failures with RHS unbound    : 0
% 20.40/20.57  # BW rewrite match attempts            : 130
% 20.40/20.57  # BW rewrite match successes           : 2
% 20.40/20.57  # Condensation attempts                : 0
% 20.40/20.57  # Condensation successes               : 0
% 20.40/20.57  # Termbank termtop insertions          : 34684714
% 20.40/20.61  
% 20.40/20.61  # -------------------------------------------------
% 20.40/20.61  # User time                : 19.862 s
% 20.40/20.61  # System time              : 0.411 s
% 20.40/20.61  # Total time               : 20.273 s
% 20.40/20.61  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
