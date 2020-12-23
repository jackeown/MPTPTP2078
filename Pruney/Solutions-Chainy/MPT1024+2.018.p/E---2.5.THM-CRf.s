%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:29 EST 2020

% Result     : Theorem 15.09s
% Output     : CNFRefutation 15.09s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 256 expanded)
%              Number of clauses        :   41 ( 106 expanded)
%              Number of leaves         :   13 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  278 (1145 expanded)
%              Number of equality atoms :   15 (  84 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

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

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X18,X19,X20,X22] :
      ( ( r2_hidden(esk2_3(X18,X19,X20),k1_relat_1(X20))
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk2_3(X18,X19,X20),X18),X20)
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(X22,k1_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X22,X18),X20)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X18,k9_relat_1(X20,X19))
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | m1_subset_1(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_17,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | m1_subset_1(k7_relset_1(X35,X36,X37,X38),k1_zfmisc_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k7_relset_1(X39,X40,X41,X42) = k9_relat_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_21,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
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

fof(c_0_23,negated_conjecture,(
    ! [X55] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))
      & ( ~ r2_hidden(X55,esk4_0)
        | ~ r2_hidden(X55,esk6_0)
        | esk8_0 != k1_funct_1(esk7_0,X55) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ( r2_hidden(X23,k1_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X24 = k1_funct_1(X25,X23)
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X23,k1_relat_1(X25))
        | X24 != k1_funct_1(X25,X23)
        | r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_26,plain,(
    ! [X43,X44,X45,X46,X47,X49] :
      ( ( m1_subset_1(esk3_5(X43,X44,X45,X46,X47),X45)
        | ~ r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))
        | ~ m1_subset_1(X47,X43)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
        | v1_xboole_0(X45)
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) )
      & ( r2_hidden(k4_tarski(esk3_5(X43,X44,X45,X46,X47),X47),X46)
        | ~ r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))
        | ~ m1_subset_1(X47,X43)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
        | v1_xboole_0(X45)
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) )
      & ( r2_hidden(esk3_5(X43,X44,X45,X46,X47),X44)
        | ~ r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))
        | ~ m1_subset_1(X47,X43)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
        | v1_xboole_0(X45)
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) )
      & ( ~ m1_subset_1(X49,X45)
        | ~ r2_hidden(k4_tarski(X49,X47),X46)
        | ~ r2_hidden(X49,X44)
        | r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))
        | ~ m1_subset_1(X47,X43)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
        | v1_xboole_0(X45)
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_30,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_36,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

fof(c_0_40,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_xboole_0(X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_xboole_0(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_41,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_44,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | esk8_0 != k1_funct_1(esk7_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,plain,
    ( k1_funct_1(X1,esk3_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_31]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_33])])).

fof(c_0_53,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_xboole_0(X32)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X32)))
      | v1_xboole_0(X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk8_0 != X3
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk4_0)
    | ~ r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk6_0)
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,esk7_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk3_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_45]),c_0_33])])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | esk8_0 != X3
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(esk3_5(X1,esk6_0,X2,esk7_0,X3),esk4_0)
    | ~ r2_hidden(X3,k7_relset_1(X2,X1,esk7_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_38])).

cnf(c_0_62,plain,
    ( r2_hidden(esk3_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_57]),c_0_38]),c_0_39])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk8_0 != X2
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r2_hidden(X2,k7_relset_1(esk4_0,X1,esk7_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_59]),c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_45]),c_0_33])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 15.09/15.28  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 15.09/15.28  # and selection function SelectMaxLComplexAvoidPosPred.
% 15.09/15.28  #
% 15.09/15.28  # Preprocessing time       : 0.029 s
% 15.09/15.28  # Presaturation interreduction done
% 15.09/15.28  
% 15.09/15.28  # Proof found!
% 15.09/15.28  # SZS status Theorem
% 15.09/15.28  # SZS output start CNFRefutation
% 15.09/15.28  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.09/15.28  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 15.09/15.28  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 15.09/15.28  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 15.09/15.28  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 15.09/15.28  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 15.09/15.28  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.09/15.28  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.09/15.28  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 15.09/15.28  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 15.09/15.28  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 15.09/15.28  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 15.09/15.28  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 15.09/15.28  fof(c_0_13, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 15.09/15.28  fof(c_0_14, plain, ![X18, X19, X20, X22]:((((r2_hidden(esk2_3(X18,X19,X20),k1_relat_1(X20))|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20))&(r2_hidden(k4_tarski(esk2_3(X18,X19,X20),X18),X20)|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20)))&(r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20)))&(~r2_hidden(X22,k1_relat_1(X20))|~r2_hidden(k4_tarski(X22,X18),X20)|~r2_hidden(X22,X19)|r2_hidden(X18,k9_relat_1(X20,X19))|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 15.09/15.28  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 15.09/15.28  fof(c_0_16, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|m1_subset_1(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 15.09/15.28  fof(c_0_17, plain, ![X35, X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|m1_subset_1(k7_relset_1(X35,X36,X37,X38),k1_zfmisc_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 15.09/15.28  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 15.09/15.28  cnf(c_0_19, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 15.09/15.28  fof(c_0_20, plain, ![X39, X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k7_relset_1(X39,X40,X41,X42)=k9_relat_1(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 15.09/15.28  fof(c_0_21, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 15.09/15.28  fof(c_0_22, plain, ![X11, X12]:(((~m1_subset_1(X12,X11)|r2_hidden(X12,X11)|v1_xboole_0(X11))&(~r2_hidden(X12,X11)|m1_subset_1(X12,X11)|v1_xboole_0(X11)))&((~m1_subset_1(X12,X11)|v1_xboole_0(X12)|~v1_xboole_0(X11))&(~v1_xboole_0(X12)|m1_subset_1(X12,X11)|~v1_xboole_0(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 15.09/15.28  fof(c_0_23, negated_conjecture, ![X55]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,esk5_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))&(~r2_hidden(X55,esk4_0)|~r2_hidden(X55,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X55)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 15.09/15.28  cnf(c_0_24, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 15.09/15.28  fof(c_0_25, plain, ![X23, X24, X25]:(((r2_hidden(X23,k1_relat_1(X25))|~r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X24=k1_funct_1(X25,X23)|~r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(~r2_hidden(X23,k1_relat_1(X25))|X24!=k1_funct_1(X25,X23)|r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 15.09/15.28  fof(c_0_26, plain, ![X43, X44, X45, X46, X47, X49]:((((m1_subset_1(esk3_5(X43,X44,X45,X46,X47),X45)|~r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))|~m1_subset_1(X47,X43)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))|v1_xboole_0(X45)|v1_xboole_0(X44)|v1_xboole_0(X43))&(r2_hidden(k4_tarski(esk3_5(X43,X44,X45,X46,X47),X47),X46)|~r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))|~m1_subset_1(X47,X43)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))|v1_xboole_0(X45)|v1_xboole_0(X44)|v1_xboole_0(X43)))&(r2_hidden(esk3_5(X43,X44,X45,X46,X47),X44)|~r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))|~m1_subset_1(X47,X43)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))|v1_xboole_0(X45)|v1_xboole_0(X44)|v1_xboole_0(X43)))&(~m1_subset_1(X49,X45)|~r2_hidden(k4_tarski(X49,X47),X46)|~r2_hidden(X49,X44)|r2_hidden(X47,k7_relset_1(X45,X43,X46,X44))|~m1_subset_1(X47,X43)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))|v1_xboole_0(X45)|v1_xboole_0(X44)|v1_xboole_0(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 15.09/15.28  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 15.09/15.28  cnf(c_0_28, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 15.09/15.28  cnf(c_0_29, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 15.09/15.28  cnf(c_0_30, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 15.09/15.28  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 15.09/15.28  cnf(c_0_32, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 15.09/15.28  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 15.09/15.28  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 15.09/15.28  cnf(c_0_35, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_18, c_0_24])).
% 15.09/15.28  cnf(c_0_36, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 15.09/15.28  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 15.09/15.28  cnf(c_0_38, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 15.09/15.28  cnf(c_0_39, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 15.09/15.28  fof(c_0_40, plain, ![X29, X30, X31]:(~v1_xboole_0(X29)|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_xboole_0(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 15.09/15.28  fof(c_0_41, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 15.09/15.28  cnf(c_0_42, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 15.09/15.28  cnf(c_0_43, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 15.09/15.28  cnf(c_0_44, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_31])).
% 15.09/15.28  cnf(c_0_45, negated_conjecture, (r2_hidden(esk8_0,k7_relset_1(esk4_0,esk5_0,esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 15.09/15.28  cnf(c_0_46, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk6_0)|esk8_0!=k1_funct_1(esk7_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 15.09/15.28  cnf(c_0_47, plain, (k1_funct_1(X1,esk3_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X2)|v1_xboole_0(X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_31]), c_0_39])).
% 15.09/15.28  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 15.09/15.28  cnf(c_0_49, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 15.09/15.28  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 15.09/15.28  cnf(c_0_51, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 15.09/15.28  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_33])])).
% 15.09/15.28  fof(c_0_53, plain, ![X32, X33, X34]:(~v1_xboole_0(X32)|(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X32)))|v1_xboole_0(X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 15.09/15.28  cnf(c_0_54, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk8_0!=X3|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk4_0)|~r2_hidden(esk3_5(X2,X4,X1,esk7_0,X3),esk6_0)|~r2_hidden(X3,k7_relset_1(X1,X2,esk7_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 15.09/15.28  cnf(c_0_55, plain, (r2_hidden(esk3_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 15.09/15.28  cnf(c_0_56, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_45]), c_0_33])])).
% 15.09/15.28  cnf(c_0_57, plain, (m1_subset_1(esk3_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 15.09/15.28  cnf(c_0_58, plain, (v1_xboole_0(X1)|~r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 15.09/15.28  cnf(c_0_59, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(sr,[status(thm)],[c_0_51, c_0_52])).
% 15.09/15.28  cnf(c_0_60, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 15.09/15.28  cnf(c_0_61, negated_conjecture, (v1_xboole_0(X1)|v1_xboole_0(X2)|esk8_0!=X3|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r2_hidden(esk3_5(X1,esk6_0,X2,esk7_0,X3),esk4_0)|~r2_hidden(X3,k7_relset_1(X2,X1,esk7_0,esk6_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_38])).
% 15.09/15.28  cnf(c_0_62, plain, (r2_hidden(esk3_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X1)|v1_xboole_0(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_57]), c_0_38]), c_0_39])).
% 15.09/15.28  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_52])).
% 15.09/15.28  cnf(c_0_64, plain, (v1_xboole_0(X1)|~r2_hidden(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_60, c_0_50])).
% 15.09/15.28  cnf(c_0_65, negated_conjecture, (v1_xboole_0(X1)|esk8_0!=X2|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r2_hidden(X2,k7_relset_1(esk4_0,X1,esk7_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 15.09/15.28  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_59]), c_0_52])).
% 15.09/15.28  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_45]), c_0_33])]), c_0_66]), ['proof']).
% 15.09/15.28  # SZS output end CNFRefutation
% 15.09/15.28  # Proof object total steps             : 68
% 15.09/15.28  # Proof object clause steps            : 41
% 15.09/15.28  # Proof object formula steps           : 27
% 15.09/15.28  # Proof object conjectures             : 19
% 15.09/15.28  # Proof object clause conjectures      : 16
% 15.09/15.28  # Proof object formula conjectures     : 3
% 15.09/15.28  # Proof object initial clauses used    : 20
% 15.09/15.28  # Proof object initial formulas used   : 13
% 15.09/15.28  # Proof object generating inferences   : 20
% 15.09/15.28  # Proof object simplifying inferences  : 22
% 15.09/15.28  # Training examples: 0 positive, 0 negative
% 15.09/15.28  # Parsed axioms                        : 13
% 15.09/15.28  # Removed by relevancy pruning/SinE    : 0
% 15.09/15.28  # Initial clauses                      : 29
% 15.09/15.28  # Removed in clause preprocessing      : 0
% 15.09/15.28  # Initial clauses in saturation        : 29
% 15.09/15.28  # Processed clauses                    : 49779
% 15.09/15.28  # ...of these trivial                  : 0
% 15.09/15.28  # ...subsumed                          : 39231
% 15.09/15.28  # ...remaining for further processing  : 10548
% 15.09/15.28  # Other redundant clauses eliminated   : 6
% 15.09/15.28  # Clauses deleted for lack of memory   : 0
% 15.09/15.28  # Backward-subsumed                    : 1602
% 15.09/15.28  # Backward-rewritten                   : 9
% 15.09/15.28  # Generated clauses                    : 519160
% 15.09/15.28  # ...of the previous two non-trivial   : 515910
% 15.09/15.28  # Contextual simplify-reflections      : 1701
% 15.09/15.28  # Paramodulations                      : 519150
% 15.09/15.28  # Factorizations                       : 0
% 15.09/15.28  # Equation resolutions                 : 8
% 15.09/15.28  # Propositional unsat checks           : 0
% 15.09/15.28  #    Propositional check models        : 0
% 15.09/15.28  #    Propositional check unsatisfiable : 0
% 15.09/15.28  #    Propositional clauses             : 0
% 15.09/15.28  #    Propositional clauses after purity: 0
% 15.09/15.28  #    Propositional unsat core size     : 0
% 15.09/15.28  #    Propositional preprocessing time  : 0.000
% 15.09/15.28  #    Propositional encoding time       : 0.000
% 15.09/15.28  #    Propositional solver time         : 0.000
% 15.09/15.28  #    Success case prop preproc time    : 0.000
% 15.09/15.28  #    Success case prop encoding time   : 0.000
% 15.09/15.28  #    Success case prop solver time     : 0.000
% 15.09/15.28  # Current number of processed clauses  : 8907
% 15.09/15.28  #    Positive orientable unit clauses  : 13
% 15.09/15.28  #    Positive unorientable unit clauses: 0
% 15.09/15.28  #    Negative unit clauses             : 11
% 15.09/15.28  #    Non-unit-clauses                  : 8883
% 15.09/15.28  # Current number of unprocessed clauses: 459798
% 15.09/15.28  # ...number of literals in the above   : 3738840
% 15.09/15.28  # Current number of archived formulas  : 0
% 15.09/15.28  # Current number of archived clauses   : 1641
% 15.09/15.28  # Clause-clause subsumption calls (NU) : 19590729
% 15.09/15.28  # Rec. Clause-clause subsumption calls : 716025
% 15.09/15.28  # Non-unit clause-clause subsumptions  : 34104
% 15.09/15.28  # Unit Clause-clause subsumption calls : 2455
% 15.09/15.28  # Rewrite failures with RHS unbound    : 0
% 15.09/15.28  # BW rewrite match attempts            : 2
% 15.09/15.28  # BW rewrite match successes           : 2
% 15.09/15.28  # Condensation attempts                : 0
% 15.09/15.28  # Condensation successes               : 0
% 15.09/15.28  # Termbank termtop insertions          : 22288902
% 15.09/15.30  
% 15.09/15.30  # -------------------------------------------------
% 15.09/15.30  # User time                : 14.627 s
% 15.09/15.30  # System time              : 0.331 s
% 15.09/15.30  # Total time               : 14.958 s
% 15.09/15.30  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
