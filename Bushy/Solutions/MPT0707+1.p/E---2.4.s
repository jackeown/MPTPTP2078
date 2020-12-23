%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t162_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:18 EDT 2019

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 576 expanded)
%              Number of clauses        :   35 ( 249 expanded)
%              Number of leaves         :   10 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 (2160 expanded)
%              Number of equality atoms :   48 ( 524 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t162_funct_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',t162_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',d12_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',dt_k6_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',existence_m1_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',t5_subset)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t162_funct_1.p',t34_funct_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t162_funct_1])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(esk3_4(X10,X11,X12,X13),k1_relat_1(X10))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk3_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X13 = k1_funct_1(X10,esk3_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X16,k1_relat_1(X10))
        | ~ r2_hidden(X16,X11)
        | X15 != k1_funct_1(X10,X16)
        | r2_hidden(X15,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk4_3(X10,X17,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X10))
        | ~ r2_hidden(X20,X17)
        | esk4_3(X10,X17,X18) != k1_funct_1(X10,X20)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),k1_relat_1(X10))
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),X17)
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk4_3(X10,X17,X18) = k1_funct_1(X10,esk5_3(X10,X17,X18))
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_12,plain,(
    ! [X46] :
      ( v1_relat_1(k6_relat_1(X46))
      & v1_funct_1(k6_relat_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_13,plain,(
    ! [X22] : v1_relat_1(k6_relat_1(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & k9_relat_1(k6_relat_1(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | ~ v1_xboole_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_19,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( X1 = k9_relat_1(k6_relat_1(X2),X3)
    | r2_hidden(esk5_3(k6_relat_1(X2),X3,X1),X3)
    | r2_hidden(esk4_3(k6_relat_1(X2),X3,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_21,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_22,plain,(
    ! [X23] : m1_subset_1(esk6_1(X23),X23) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_23,plain,(
    ! [X35,X36,X37] :
      ( ~ r2_hidden(X35,X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(X37))
      | m1_subset_1(X35,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_24,plain,(
    ! [X38,X39,X40] :
      ( ~ r2_hidden(X38,X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(X40))
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk2_0)
    | r2_hidden(esk5_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk2_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_25])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,plain,(
    ! [X29,X30,X31] :
      ( ( k1_relat_1(X30) = X29
        | X30 != k6_relat_1(X29)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( ~ r2_hidden(X31,X29)
        | k1_funct_1(X30,X31) = X31
        | X30 != k6_relat_1(X29)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( r2_hidden(esk7_2(X29,X30),X29)
        | k1_relat_1(X30) != X29
        | X30 = k6_relat_1(X29)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( k1_funct_1(X30,esk7_2(X29,X30)) != esk7_2(X29,X30)
        | k1_relat_1(X30) != X29
        | X30 = k6_relat_1(X29)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k1_funct_1(X3,X1) = X1
    | ~ r2_hidden(X1,X2)
    | X3 != k6_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk2_0)
    | m1_subset_1(esk5_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( esk4_3(X1,X2,X3) = k1_funct_1(X1,esk5_3(X1,X2,X3))
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( k1_funct_1(k6_relat_1(X1),X2) = X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_16]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk2_0)
    | r2_hidden(esk5_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( k1_funct_1(k6_relat_1(X1),esk5_3(k6_relat_1(X1),X2,X3)) = esk4_3(k6_relat_1(X1),X2,X3)
    | X3 = k9_relat_1(k6_relat_1(X1),X2)
    | r2_hidden(esk4_3(k6_relat_1(X1),X2,X3),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_16]),c_0_17])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k6_relat_1(esk1_0),esk5_3(k6_relat_1(esk1_0),esk2_0,esk2_0)) = esk5_3(k6_relat_1(esk1_0),esk2_0,esk2_0)
    | r2_hidden(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( esk5_3(k6_relat_1(esk1_0),esk2_0,esk2_0) = esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0)
    | r2_hidden(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_46])).

cnf(c_0_48,plain,
    ( k1_relat_1(X1) = X2
    | X1 != k6_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_47])).

cnf(c_0_50,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,k1_relat_1(X1))
    | ~ r2_hidden(X4,X2)
    | esk4_3(X1,X2,X3) != k1_funct_1(X1,X4)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_16]),c_0_17])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_49]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0) != k1_funct_1(k6_relat_1(esk1_0),X1)
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_16]),c_0_17]),c_0_51])]),c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(k6_relat_1(esk1_0),esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0)) = esk4_3(k6_relat_1(esk1_0),esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_52]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
