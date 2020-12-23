%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:37 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 359 expanded)
%              Number of clauses        :   45 ( 151 expanded)
%              Number of leaves         :   13 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  279 (1508 expanded)
%              Number of equality atoms :   16 ( 137 expanded)
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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X36,X37,X38] :
      ( ( v4_relat_1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v5_relat_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_15,negated_conjecture,(
    ! [X59] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ m1_subset_1(X59,esk5_0)
        | ~ r2_hidden(X59,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X59) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | v1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( ( ~ v4_relat_1(X24,X23)
        | r1_tarski(k1_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k1_relat_1(X24),X23)
        | v4_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_18,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k7_relset_1(X43,X44,X45,X46) = k9_relat_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_22,plain,(
    ! [X25,X26,X27,X29] :
      ( ( r2_hidden(esk3_3(X25,X26,X27),k1_relat_1(X27))
        | ~ r2_hidden(X25,k9_relat_1(X27,X26))
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk3_3(X25,X26,X27),X25),X27)
        | ~ r2_hidden(X25,k9_relat_1(X27,X26))
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X26)
        | ~ r2_hidden(X25,k9_relat_1(X27,X26))
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(X29,k1_relat_1(X27))
        | ~ r2_hidden(k4_tarski(X29,X25),X27)
        | ~ r2_hidden(X29,X26)
        | r2_hidden(X25,k9_relat_1(X27,X26))
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_23,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v4_relat_1(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_27,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

fof(c_0_36,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_37,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | m1_subset_1(k7_relset_1(X39,X40,X41,X42),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_38,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_3(X1,X4,X2),X3)
    | ~ r2_hidden(X1,k9_relat_1(X2,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(X1,X2,esk8_0,esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19])])).

fof(c_0_44,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X31 = k1_funct_1(X32,X30)
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X30,k1_relat_1(X32))
        | X31 != k1_funct_1(X32,X30)
        | r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_45,plain,(
    ! [X47,X48,X49,X50,X51,X53] :
      ( ( m1_subset_1(esk4_5(X47,X48,X49,X50,X51),X49)
        | ~ r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))
        | ~ m1_subset_1(X51,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X48)
        | v1_xboole_0(X47) )
      & ( r2_hidden(k4_tarski(esk4_5(X47,X48,X49,X50,X51),X51),X50)
        | ~ r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))
        | ~ m1_subset_1(X51,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X48)
        | v1_xboole_0(X47) )
      & ( r2_hidden(esk4_5(X47,X48,X49,X50,X51),X48)
        | ~ r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))
        | ~ m1_subset_1(X51,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X48)
        | v1_xboole_0(X47) )
      & ( ~ m1_subset_1(X53,X49)
        | ~ r2_hidden(k4_tarski(X53,X51),X50)
        | ~ r2_hidden(X53,X48)
        | r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))
        | ~ m1_subset_1(X51,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X48)
        | v1_xboole_0(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,esk5_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_3(X1,X3,X2),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k9_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_52,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X1,k7_relset_1(X4,X2,X3,X5)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_56,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))
    | ~ v1_xboole_0(X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(esk8_0,esk5_0))
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_26])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,plain,
    ( k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5)) = X5
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ r2_hidden(X5,k7_relset_1(X4,X2,X1,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_20]),c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(X1)
    | esk9_0 != X2
    | ~ m1_subset_1(esk4_5(X3,X4,X1,esk8_0,X2),esk5_0)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r2_hidden(esk4_5(X3,X4,X1,esk8_0,X2),esk7_0)
    | ~ r2_hidden(X2,k7_relset_1(X1,X3,esk8_0,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_62]),c_0_26])])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( esk9_0 != X1
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ r2_hidden(esk4_5(X2,X3,esk5_0,esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_54]),c_0_66]),c_0_56])).

cnf(c_0_68,plain,
    ( r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_58]),c_0_26])])).

cnf(c_0_70,negated_conjecture,
    ( esk9_0 != X1
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_65]),c_0_69]),c_0_54]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_34]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:30:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.24/1.46  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 1.24/1.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.24/1.46  #
% 1.24/1.46  # Preprocessing time       : 0.041 s
% 1.24/1.46  # Presaturation interreduction done
% 1.24/1.46  
% 1.24/1.46  # Proof found!
% 1.24/1.46  # SZS status Theorem
% 1.24/1.46  # SZS output start CNFRefutation
% 1.24/1.46  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 1.24/1.46  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.24/1.46  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.24/1.46  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.24/1.46  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.24/1.46  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.24/1.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.24/1.46  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.24/1.46  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.24/1.46  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 1.24/1.46  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.24/1.46  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.24/1.46  fof(t52_relset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 1.24/1.46  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 1.24/1.46  fof(c_0_14, plain, ![X36, X37, X38]:((v4_relat_1(X38,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v5_relat_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.24/1.46  fof(c_0_15, negated_conjecture, ![X59]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~m1_subset_1(X59,esk5_0)|(~r2_hidden(X59,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X59))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 1.24/1.46  fof(c_0_16, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.24/1.46  fof(c_0_17, plain, ![X23, X24]:((~v4_relat_1(X24,X23)|r1_tarski(k1_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_tarski(k1_relat_1(X24),X23)|v4_relat_1(X24,X23)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.24/1.46  cnf(c_0_18, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.24/1.46  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.24/1.46  cnf(c_0_20, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.24/1.46  fof(c_0_21, plain, ![X43, X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k7_relset_1(X43,X44,X45,X46)=k9_relat_1(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 1.24/1.46  fof(c_0_22, plain, ![X25, X26, X27, X29]:((((r2_hidden(esk3_3(X25,X26,X27),k1_relat_1(X27))|~r2_hidden(X25,k9_relat_1(X27,X26))|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk3_3(X25,X26,X27),X25),X27)|~r2_hidden(X25,k9_relat_1(X27,X26))|~v1_relat_1(X27)))&(r2_hidden(esk3_3(X25,X26,X27),X26)|~r2_hidden(X25,k9_relat_1(X27,X26))|~v1_relat_1(X27)))&(~r2_hidden(X29,k1_relat_1(X27))|~r2_hidden(k4_tarski(X29,X25),X27)|~r2_hidden(X29,X26)|r2_hidden(X25,k9_relat_1(X27,X26))|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 1.24/1.46  fof(c_0_23, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.24/1.46  cnf(c_0_24, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.24/1.46  cnf(c_0_25, negated_conjecture, (v4_relat_1(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.24/1.46  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 1.24/1.46  cnf(c_0_27, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.24/1.46  fof(c_0_28, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.24/1.46  cnf(c_0_29, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.24/1.46  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.24/1.46  cnf(c_0_31, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.24/1.46  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.24/1.46  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 1.24/1.46  cnf(c_0_34, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.24/1.46  cnf(c_0_35, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 1.24/1.46  fof(c_0_36, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.24/1.46  fof(c_0_37, plain, ![X39, X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|m1_subset_1(k7_relset_1(X39,X40,X41,X42),k1_zfmisc_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 1.24/1.46  fof(c_0_38, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|~v1_xboole_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 1.24/1.46  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.24/1.46  cnf(c_0_40, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.24/1.46  cnf(c_0_41, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(esk3_3(X1,X4,X2),X3)|~r2_hidden(X1,k9_relat_1(X2,X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 1.24/1.46  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.24/1.46  cnf(c_0_43, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(X1,X2,esk8_0,esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19])])).
% 1.24/1.46  fof(c_0_44, plain, ![X30, X31, X32]:(((r2_hidden(X30,k1_relat_1(X32))|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(X31=k1_funct_1(X32,X30)|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(~r2_hidden(X30,k1_relat_1(X32))|X31!=k1_funct_1(X32,X30)|r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 1.24/1.46  fof(c_0_45, plain, ![X47, X48, X49, X50, X51, X53]:((((m1_subset_1(esk4_5(X47,X48,X49,X50,X51),X49)|~r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))|~m1_subset_1(X51,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))|v1_xboole_0(X49)|v1_xboole_0(X48)|v1_xboole_0(X47))&(r2_hidden(k4_tarski(esk4_5(X47,X48,X49,X50,X51),X51),X50)|~r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))|~m1_subset_1(X51,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))|v1_xboole_0(X49)|v1_xboole_0(X48)|v1_xboole_0(X47)))&(r2_hidden(esk4_5(X47,X48,X49,X50,X51),X48)|~r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))|~m1_subset_1(X51,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))|v1_xboole_0(X49)|v1_xboole_0(X48)|v1_xboole_0(X47)))&(~m1_subset_1(X53,X49)|~r2_hidden(k4_tarski(X53,X51),X50)|~r2_hidden(X53,X48)|r2_hidden(X51,k7_relset_1(X49,X47,X50,X48))|~m1_subset_1(X51,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))|v1_xboole_0(X49)|v1_xboole_0(X48)|v1_xboole_0(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_relset_1])])])])])])).
% 1.24/1.46  cnf(c_0_46, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.24/1.46  cnf(c_0_47, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.24/1.46  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.24/1.46  cnf(c_0_49, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.24/1.46  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,esk5_0))|~v1_relat_1(X2)|~r2_hidden(esk3_3(X1,X3,X2),k1_relat_1(esk8_0))|~r2_hidden(X1,k9_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.24/1.46  cnf(c_0_51, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_27])).
% 1.24/1.46  cnf(c_0_52, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.24/1.46  cnf(c_0_53, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.24/1.46  cnf(c_0_54, plain, (m1_subset_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X1,k7_relset_1(X4,X2,X3,X5))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.24/1.46  cnf(c_0_55, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 1.24/1.46  cnf(c_0_56, plain, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k7_relset_1(X2,X3,X1,X5))|~v1_xboole_0(X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_20])).
% 1.24/1.46  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,k9_relat_1(esk8_0,esk5_0))|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_26])])).
% 1.24/1.46  cnf(c_0_58, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_51, c_0_19])).
% 1.24/1.46  cnf(c_0_59, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.24/1.46  cnf(c_0_60, plain, (k1_funct_1(X1,esk4_5(X2,X3,X4,X1,X5))=X5|v1_xboole_0(X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~r2_hidden(X5,k7_relset_1(X4,X2,X1,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_20]), c_0_55]), c_0_56])).
% 1.24/1.46  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.24/1.46  cnf(c_0_62, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.24/1.46  cnf(c_0_63, negated_conjecture, (v1_xboole_0(X1)|esk9_0!=X2|~m1_subset_1(esk4_5(X3,X4,X1,esk8_0,X2),esk5_0)|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~r2_hidden(esk4_5(X3,X4,X1,esk8_0,X2),esk7_0)|~r2_hidden(X2,k7_relset_1(X1,X3,esk8_0,X4))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 1.24/1.46  cnf(c_0_64, plain, (m1_subset_1(esk4_5(X1,X2,X3,X4,X5),X3)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.24/1.46  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_62]), c_0_26])])).
% 1.24/1.46  cnf(c_0_66, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_55, c_0_43])).
% 1.24/1.46  cnf(c_0_67, negated_conjecture, (esk9_0!=X1|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~r2_hidden(esk4_5(X2,X3,esk5_0,esk8_0,X1),esk7_0)|~r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_54]), c_0_66]), c_0_56])).
% 1.24/1.46  cnf(c_0_68, plain, (r2_hidden(esk4_5(X1,X2,X3,X4,X5),X2)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|~r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))|~m1_subset_1(X5,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.24/1.46  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_58]), c_0_26])])).
% 1.24/1.46  cnf(c_0_70, negated_conjecture, (esk9_0!=X1|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~r2_hidden(X1,k7_relset_1(esk5_0,X2,esk8_0,esk7_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_65]), c_0_69]), c_0_54]), c_0_66])).
% 1.24/1.46  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_34]), c_0_19])]), ['proof']).
% 1.24/1.46  # SZS output end CNFRefutation
% 1.24/1.46  # Proof object total steps             : 72
% 1.24/1.46  # Proof object clause steps            : 45
% 1.24/1.46  # Proof object formula steps           : 27
% 1.24/1.46  # Proof object conjectures             : 24
% 1.24/1.46  # Proof object clause conjectures      : 21
% 1.24/1.46  # Proof object formula conjectures     : 3
% 1.24/1.46  # Proof object initial clauses used    : 21
% 1.24/1.46  # Proof object initial formulas used   : 13
% 1.24/1.46  # Proof object generating inferences   : 24
% 1.24/1.46  # Proof object simplifying inferences  : 28
% 1.24/1.46  # Training examples: 0 positive, 0 negative
% 1.24/1.46  # Parsed axioms                        : 13
% 1.24/1.46  # Removed by relevancy pruning/SinE    : 0
% 1.24/1.46  # Initial clauses                      : 30
% 1.24/1.46  # Removed in clause preprocessing      : 0
% 1.24/1.46  # Initial clauses in saturation        : 30
% 1.24/1.46  # Processed clauses                    : 8430
% 1.24/1.46  # ...of these trivial                  : 1
% 1.24/1.46  # ...subsumed                          : 6408
% 1.24/1.46  # ...remaining for further processing  : 2021
% 1.24/1.46  # Other redundant clauses eliminated   : 6
% 1.24/1.46  # Clauses deleted for lack of memory   : 0
% 1.24/1.46  # Backward-subsumed                    : 138
% 1.24/1.46  # Backward-rewritten                   : 1
% 1.24/1.46  # Generated clauses                    : 37172
% 1.24/1.46  # ...of the previous two non-trivial   : 37096
% 1.24/1.46  # Contextual simplify-reflections      : 648
% 1.24/1.46  # Paramodulations                      : 37165
% 1.24/1.46  # Factorizations                       : 0
% 1.24/1.46  # Equation resolutions                 : 7
% 1.24/1.46  # Propositional unsat checks           : 0
% 1.24/1.46  #    Propositional check models        : 0
% 1.24/1.46  #    Propositional check unsatisfiable : 0
% 1.24/1.46  #    Propositional clauses             : 0
% 1.24/1.46  #    Propositional clauses after purity: 0
% 1.24/1.46  #    Propositional unsat core size     : 0
% 1.24/1.46  #    Propositional preprocessing time  : 0.000
% 1.24/1.46  #    Propositional encoding time       : 0.000
% 1.24/1.46  #    Propositional solver time         : 0.000
% 1.24/1.46  #    Success case prop preproc time    : 0.000
% 1.24/1.46  #    Success case prop encoding time   : 0.000
% 1.24/1.46  #    Success case prop solver time     : 0.000
% 1.24/1.46  # Current number of processed clauses  : 1852
% 1.24/1.46  #    Positive orientable unit clauses  : 16
% 1.24/1.46  #    Positive unorientable unit clauses: 0
% 1.24/1.46  #    Negative unit clauses             : 9
% 1.24/1.46  #    Non-unit-clauses                  : 1827
% 1.24/1.46  # Current number of unprocessed clauses: 28472
% 1.24/1.46  # ...number of literals in the above   : 197075
% 1.24/1.46  # Current number of archived formulas  : 0
% 1.24/1.46  # Current number of archived clauses   : 169
% 1.24/1.46  # Clause-clause subsumption calls (NU) : 1006217
% 1.24/1.46  # Rec. Clause-clause subsumption calls : 100391
% 1.24/1.46  # Non-unit clause-clause subsumptions  : 4902
% 1.24/1.46  # Unit Clause-clause subsumption calls : 514
% 1.24/1.46  # Rewrite failures with RHS unbound    : 0
% 1.24/1.46  # BW rewrite match attempts            : 5
% 1.24/1.46  # BW rewrite match successes           : 1
% 1.24/1.46  # Condensation attempts                : 0
% 1.24/1.46  # Condensation successes               : 0
% 1.24/1.46  # Termbank termtop insertions          : 1054013
% 1.24/1.46  
% 1.24/1.46  # -------------------------------------------------
% 1.24/1.46  # User time                : 1.104 s
% 1.24/1.46  # System time              : 0.016 s
% 1.24/1.46  # Total time               : 1.120 s
% 1.24/1.46  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
