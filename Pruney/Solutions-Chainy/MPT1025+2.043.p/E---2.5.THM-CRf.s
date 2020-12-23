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
% DateTime   : Thu Dec  3 11:06:41 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 371 expanded)
%              Number of clauses        :   42 ( 151 expanded)
%              Number of leaves         :   14 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 (1604 expanded)
%              Number of equality atoms :   15 ( 129 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_16,plain,(
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

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X12,X11)
        | r2_hidden(X12,X11)
        | v1_xboole_0(X11) )
      & ( ~ r2_hidden(X12,X11)
        | m1_subset_1(X12,X11)
        | v1_xboole_0(X11) )
      & ( ~ m1_subset_1(X12,X11)
        | v1_xboole_0(X12)
        | ~ v1_xboole_0(X11) )
      & ( ~ v1_xboole_0(X12)
        | m1_subset_1(X12,X11)
        | ~ v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_18,negated_conjecture,(
    ! [X56] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))
      & ( ~ m1_subset_1(X56,esk4_0)
        | ~ r2_hidden(X56,esk6_0)
        | esk8_0 != k1_funct_1(esk7_0,X56) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k7_relset_1(X40,X41,X42,X43) = k9_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_22,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | v1_relat_1(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_23,plain,(
    ! [X20,X21] : v1_relat_1(k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_24,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_25,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | m1_subset_1(k7_relset_1(X36,X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_31,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X28 = k1_funct_1(X29,X27)
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X27,k1_relat_1(X29))
        | X28 != k1_funct_1(X29,X27)
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_35,plain,(
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

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

fof(c_0_39,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_xboole_0(X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_40,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_43,plain,
    ( ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_33])])).

cnf(c_0_46,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,plain,
    ( ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_28])])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | esk8_0 != k1_funct_1(esk7_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,plain,
    ( k1_funct_1(X1,esk3_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_59,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_xboole_0(X33)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33)))
      | v1_xboole_0(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk8_0 != X3
    | ~ m1_subset_1(esk3_5(X2,X4,X1,esk7_0,X3),esk4_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk6_0)
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,esk7_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_45])])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_53])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk8_0 != X3
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))
    | ~ r2_hidden(esk3_5(X2,X1,esk4_0,esk7_0,X3),esk6_0)
    | ~ r2_hidden(X3,k7_relset_1(esk4_0,X2,esk7_0,X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_48])).

cnf(c_0_65,plain,
    ( r2_hidden(esk3_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_45]),c_0_28])])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk8_0 != X2
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r2_hidden(X2,k7_relset_1(esk4_0,X1,esk7_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_62]),c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_58]),c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_44]),c_0_28])]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 2.43/2.60  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 2.43/2.60  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.43/2.60  #
% 2.43/2.60  # Preprocessing time       : 0.029 s
% 2.43/2.60  # Presaturation interreduction done
% 2.43/2.60  
% 2.43/2.60  # Proof found!
% 2.43/2.60  # SZS status Theorem
% 2.43/2.60  # SZS output start CNFRefutation
% 2.43/2.60  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.43/2.60  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.43/2.60  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.43/2.60  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.43/2.60  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.43/2.60  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.43/2.60  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.43/2.60  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.43/2.60  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.43/2.60  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.43/2.60  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 2.43/2.60  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.43/2.60  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.43/2.60  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.43/2.60  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 2.43/2.60  fof(c_0_15, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 2.43/2.60  fof(c_0_16, plain, ![X22, X23, X24, X26]:((((r2_hidden(esk2_3(X22,X23,X24),k1_relat_1(X24))|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk2_3(X22,X23,X24),X22),X24)|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24)))&(r2_hidden(esk2_3(X22,X23,X24),X23)|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24)))&(~r2_hidden(X26,k1_relat_1(X24))|~r2_hidden(k4_tarski(X26,X22),X24)|~r2_hidden(X26,X23)|r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 2.43/2.60  fof(c_0_17, plain, ![X11, X12]:(((~m1_subset_1(X12,X11)|r2_hidden(X12,X11)|v1_xboole_0(X11))&(~r2_hidden(X12,X11)|m1_subset_1(X12,X11)|v1_xboole_0(X11)))&((~m1_subset_1(X12,X11)|v1_xboole_0(X12)|~v1_xboole_0(X11))&(~v1_xboole_0(X12)|m1_subset_1(X12,X11)|~v1_xboole_0(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 2.43/2.60  fof(c_0_18, negated_conjecture, ![X56]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))&(~m1_subset_1(X56,esk4_0)|(~r2_hidden(X56,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X56))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 2.43/2.60  cnf(c_0_19, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.43/2.60  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.43/2.60  fof(c_0_21, plain, ![X40, X41, X42, X43]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k7_relset_1(X40,X41,X42,X43)=k9_relat_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 2.43/2.60  fof(c_0_22, plain, ![X18, X19]:(~v1_relat_1(X18)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|v1_relat_1(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 2.43/2.60  fof(c_0_23, plain, ![X20, X21]:v1_relat_1(k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 2.43/2.60  fof(c_0_24, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 2.43/2.60  fof(c_0_25, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|m1_subset_1(k7_relset_1(X36,X37,X38,X39),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 2.43/2.60  cnf(c_0_26, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.43/2.60  cnf(c_0_27, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.43/2.60  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.43/2.60  cnf(c_0_29, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.43/2.60  cnf(c_0_30, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.43/2.60  cnf(c_0_31, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.43/2.60  cnf(c_0_32, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.43/2.60  cnf(c_0_33, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.43/2.60  fof(c_0_34, plain, ![X27, X28, X29]:(((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X28=k1_funct_1(X29,X27)|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X27,k1_relat_1(X29))|X28!=k1_funct_1(X29,X27)|r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 2.43/2.60  fof(c_0_35, plain, ![X44, X45, X46, X47, X48, X50]:((((m1_subset_1(esk3_5(X44,X45,X46,X47,X48),X46)|~r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44))&(r2_hidden(k4_tarski(esk3_5(X44,X45,X46,X47,X48),X48),X47)|~r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44)))&(r2_hidden(esk3_5(X44,X45,X46,X47,X48),X45)|~r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44)))&(~m1_subset_1(X50,X46)|~r2_hidden(k4_tarski(X50,X48),X47)|~r2_hidden(X50,X45)|r2_hidden(X48,k7_relset_1(X46,X44,X47,X45))|~m1_subset_1(X48,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))|v1_xboole_0(X46)|v1_xboole_0(X45)|v1_xboole_0(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 2.43/2.60  cnf(c_0_36, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.43/2.60  cnf(c_0_37, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.43/2.60  cnf(c_0_38, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_19, c_0_26])).
% 2.43/2.60  fof(c_0_39, plain, ![X30, X31, X32]:(~v1_xboole_0(X30)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 2.43/2.60  fof(c_0_40, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 2.43/2.60  cnf(c_0_41, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.43/2.60  cnf(c_0_42, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 2.43/2.60  cnf(c_0_43, plain, (~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.43/2.60  cnf(c_0_44, negated_conjecture, (r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.43/2.60  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_33])])).
% 2.43/2.60  cnf(c_0_46, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.43/2.60  cnf(c_0_47, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.43/2.60  cnf(c_0_48, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 2.43/2.60  cnf(c_0_49, plain, (~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 2.43/2.60  cnf(c_0_50, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.43/2.60  cnf(c_0_51, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.43/2.60  cnf(c_0_52, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.43/2.60  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_28])])).
% 2.43/2.60  cnf(c_0_54, negated_conjecture, (~m1_subset_1(X1,esk4_0)|~r2_hidden(X1,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.43/2.60  cnf(c_0_55, plain, (k1_funct_1(X1,esk3_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])).
% 2.43/2.60  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.43/2.60  cnf(c_0_57, plain, (v1_xboole_0(X1)|~r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.43/2.60  cnf(c_0_58, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[c_0_52, c_0_53])).
% 2.43/2.60  fof(c_0_59, plain, ![X33, X34, X35]:(~v1_xboole_0(X33)|(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33)))|v1_xboole_0(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 2.43/2.60  cnf(c_0_60, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk8_0!=X3|~m1_subset_1(esk3_5(X2,X4,X1,esk7_0,X3),esk4_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk6_0)|~r2_hidden(X3,k7_relset_1(X1,X2,esk7_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_45])])).
% 2.43/2.60  cnf(c_0_61, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.43/2.60  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_53])).
% 2.43/2.60  cnf(c_0_63, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.43/2.60  cnf(c_0_64, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk8_0!=X3|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~r2_hidden(esk3_5(X2,X1,esk4_0,esk7_0,X3),esk6_0)|~r2_hidden(X3,k7_relset_1(esk4_0,X2,esk7_0,X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_48])).
% 2.43/2.60  cnf(c_0_65, plain, (r2_hidden(esk3_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.43/2.60  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_45]), c_0_28])])).
% 2.43/2.60  cnf(c_0_67, plain, (v1_xboole_0(X1)|~r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_63, c_0_51])).
% 2.43/2.60  cnf(c_0_68, negated_conjecture, (v1_xboole_0(X1)|esk8_0!=X2|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r2_hidden(X2,k7_relset_1(esk4_0,X1,esk7_0,esk6_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_62]), c_0_48])).
% 2.43/2.60  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_58]), c_0_53])).
% 2.43/2.60  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_44]), c_0_28])]), c_0_69]), ['proof']).
% 2.43/2.60  # SZS output end CNFRefutation
% 2.43/2.60  # Proof object total steps             : 71
% 2.43/2.60  # Proof object clause steps            : 42
% 2.43/2.60  # Proof object formula steps           : 29
% 2.43/2.60  # Proof object conjectures             : 20
% 2.43/2.60  # Proof object clause conjectures      : 17
% 2.43/2.60  # Proof object formula conjectures     : 3
% 2.43/2.60  # Proof object initial clauses used    : 21
% 2.43/2.60  # Proof object initial formulas used   : 14
% 2.43/2.60  # Proof object generating inferences   : 20
% 2.43/2.60  # Proof object simplifying inferences  : 24
% 2.43/2.60  # Training examples: 0 positive, 0 negative
% 2.43/2.60  # Parsed axioms                        : 14
% 2.43/2.60  # Removed by relevancy pruning/SinE    : 0
% 2.43/2.60  # Initial clauses                      : 30
% 2.43/2.60  # Removed in clause preprocessing      : 0
% 2.43/2.60  # Initial clauses in saturation        : 30
% 2.43/2.60  # Processed clauses                    : 12197
% 2.43/2.60  # ...of these trivial                  : 0
% 2.43/2.60  # ...subsumed                          : 8962
% 2.43/2.60  # ...remaining for further processing  : 3235
% 2.43/2.60  # Other redundant clauses eliminated   : 6
% 2.43/2.60  # Clauses deleted for lack of memory   : 0
% 2.43/2.60  # Backward-subsumed                    : 168
% 2.43/2.60  # Backward-rewritten                   : 5
% 2.43/2.60  # Generated clauses                    : 71224
% 2.43/2.60  # ...of the previous two non-trivial   : 70861
% 2.43/2.60  # Contextual simplify-reflections      : 308
% 2.43/2.60  # Paramodulations                      : 71214
% 2.43/2.60  # Factorizations                       : 0
% 2.43/2.60  # Equation resolutions                 : 8
% 2.43/2.60  # Propositional unsat checks           : 0
% 2.43/2.60  #    Propositional check models        : 0
% 2.43/2.60  #    Propositional check unsatisfiable : 0
% 2.43/2.60  #    Propositional clauses             : 0
% 2.43/2.60  #    Propositional clauses after purity: 0
% 2.43/2.60  #    Propositional unsat core size     : 0
% 2.43/2.60  #    Propositional preprocessing time  : 0.000
% 2.43/2.60  #    Propositional encoding time       : 0.000
% 2.43/2.60  #    Propositional solver time         : 0.000
% 2.43/2.60  #    Success case prop preproc time    : 0.000
% 2.43/2.60  #    Success case prop encoding time   : 0.000
% 2.43/2.60  #    Success case prop solver time     : 0.000
% 2.43/2.60  # Current number of processed clauses  : 3031
% 2.43/2.60  #    Positive orientable unit clauses  : 13
% 2.43/2.60  #    Positive unorientable unit clauses: 0
% 2.43/2.60  #    Negative unit clauses             : 10
% 2.43/2.60  #    Non-unit-clauses                  : 3008
% 2.43/2.60  # Current number of unprocessed clauses: 58075
% 2.43/2.60  # ...number of literals in the above   : 518369
% 2.43/2.60  # Current number of archived formulas  : 0
% 2.43/2.60  # Current number of archived clauses   : 204
% 2.43/2.60  # Clause-clause subsumption calls (NU) : 1962057
% 2.43/2.60  # Rec. Clause-clause subsumption calls : 120661
% 2.43/2.60  # Non-unit clause-clause subsumptions  : 8108
% 2.43/2.60  # Unit Clause-clause subsumption calls : 131
% 2.43/2.60  # Rewrite failures with RHS unbound    : 0
% 2.43/2.60  # BW rewrite match attempts            : 2
% 2.43/2.60  # BW rewrite match successes           : 2
% 2.43/2.60  # Condensation attempts                : 0
% 2.43/2.60  # Condensation successes               : 0
% 2.43/2.60  # Termbank termtop insertions          : 2522995
% 2.43/2.60  
% 2.43/2.60  # -------------------------------------------------
% 2.43/2.60  # User time                : 2.213 s
% 2.43/2.60  # System time              : 0.048 s
% 2.43/2.60  # Total time               : 2.261 s
% 2.43/2.60  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
