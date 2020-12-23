%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t18_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:21 EDT 2019

% Result     : Theorem 231.38s
% Output     : CNFRefutation 231.38s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 126 expanded)
%              Number of clauses        :   38 (  56 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 488 expanded)
%              Number of equality atoms :   43 ( 149 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',d5_funct_1)).

fof(s3_funct_1__e1_27_1__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X2
      & ! [X4] :
          ( r2_hidden(X4,X2)
         => k1_funct_1(X3,X4) = o_1_0_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',s3_funct_1__e1_27_1__funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',t2_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',d3_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',existence_m1_subset_1)).

fof(dt_o_1_0_funct_1,axiom,(
    ! [X1] : m1_subset_1(o_1_0_funct_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',dt_o_1_0_funct_1)).

fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',t18_funct_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',t6_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t18_funct_1.p',fc1_xboole_0)).

fof(c_0_12,plain,(
    ! [X16,X17,X18,X20,X21,X22,X24] :
      ( ( r2_hidden(esk4_3(X16,X17,X18),k1_relat_1(X16))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X18 = k1_funct_1(X16,esk4_3(X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X21,k1_relat_1(X16))
        | X20 != k1_funct_1(X16,X21)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk5_2(X16,X22),X22)
        | ~ r2_hidden(X24,k1_relat_1(X16))
        | esk5_2(X16,X22) != k1_funct_1(X16,X24)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk6_2(X16,X22),k1_relat_1(X16))
        | r2_hidden(esk5_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( esk5_2(X16,X22) = k1_funct_1(X16,esk6_2(X16,X22))
        | r2_hidden(esk5_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_13,plain,(
    ! [X29,X30,X32] :
      ( v1_relat_1(esk8_2(X29,X30))
      & v1_funct_1(esk8_2(X29,X30))
      & k1_relat_1(esk8_2(X29,X30)) = X30
      & ( ~ r2_hidden(X32,X30)
        | k1_funct_1(esk8_2(X29,X30),X32) = o_1_0_funct_1(X29) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e1_27_1__funct_1])])])])).

cnf(c_0_14,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,plain,(
    ! [X37] : r1_tarski(k1_xboole_0,X37) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_18,plain,
    ( k1_funct_1(esk8_2(X3,X2),X1) = o_1_0_funct_1(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_funct_1(esk8_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_relat_1(esk8_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_relat_1(esk8_2(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X43,X44,X45] :
      ( ~ r2_hidden(X43,X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X45))
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( X1 = o_1_0_funct_1(X2)
    | ~ r2_hidden(esk4_3(esk8_2(X2,X3),k2_relat_1(esk8_2(X2,X3)),X1),X3)
    | ~ r2_hidden(X1,k2_relat_1(esk8_2(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_3(esk8_2(X1,X2),k2_relat_1(esk8_2(X1,X2)),X3),X2)
    | ~ r2_hidden(X3,k2_relat_1(esk8_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_20]),c_0_21])])).

fof(c_0_29,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk3_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X35,X36)
      | v1_xboole_0(X36)
      | r2_hidden(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_33,plain,(
    ! [X27] : m1_subset_1(esk7_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_34,plain,
    ( X1 = o_1_0_funct_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(esk8_2(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X26] : m1_subset_1(o_1_0_funct_1(X26),X26) ),
    inference(variable_rename,[status(thm)],[dt_o_1_0_funct_1])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( esk3_2(k2_relat_1(esk8_2(X1,X2)),X3) = o_1_0_funct_1(X1)
    | r1_tarski(k2_relat_1(esk8_2(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( m1_subset_1(o_1_0_funct_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(esk8_2(X3,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_46,negated_conjecture,(
    ! [X7] :
      ( ( esk1_0 != k1_xboole_0
        | esk2_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | esk2_0 != k1_relat_1(X7)
        | ~ r1_tarski(k2_relat_1(X7),esk1_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_relat_1(esk8_2(X1,X2)),X3)
    | ~ r2_hidden(o_1_0_funct_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(o_1_0_funct_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

fof(c_0_49,plain,(
    ! [X46] :
      ( ~ v1_xboole_0(X46)
      | X46 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k2_relat_1(esk8_2(X1,k1_xboole_0)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk2_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(k2_relat_1(esk8_2(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k2_relat_1(esk8_2(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk1_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_23]),c_0_20]),c_0_21])])])).

cnf(c_0_57,plain,
    ( k2_relat_1(esk8_2(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_57]),c_0_23]),c_0_26]),c_0_20]),c_0_21])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
