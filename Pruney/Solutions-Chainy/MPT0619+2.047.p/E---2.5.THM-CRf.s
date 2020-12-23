%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 177 expanded)
%              Number of clauses        :   47 (  79 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 460 expanded)
%              Number of equality atoms :   58 ( 189 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X29,X30,X31,X33] :
      ( ( r2_hidden(esk2_3(X25,X26,X27),k1_relat_1(X25))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X27 = k1_funct_1(X25,esk2_3(X25,X26,X27))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X30,k1_relat_1(X25))
        | X29 != k1_funct_1(X25,X30)
        | r2_hidden(X29,X26)
        | X26 != k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(esk3_2(X25,X31),X31)
        | ~ r2_hidden(X33,k1_relat_1(X25))
        | esk3_2(X25,X31) != k1_funct_1(X25,X33)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk4_2(X25,X31),k1_relat_1(X25))
        | r2_hidden(esk3_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( esk3_2(X25,X31) = k1_funct_1(X25,esk4_2(X25,X31))
        | r2_hidden(esk3_2(X25,X31),X31)
        | X31 = k2_relat_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & k1_relat_1(esk6_0) = k1_tarski(esk5_0)
    & k2_relat_1(esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(k1_tarski(X20),k1_tarski(X21))
      | X20 = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

fof(c_0_16,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ( ~ r1_tarski(k1_tarski(X12),X13)
        | r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X12,X13)
        | r1_tarski(k1_tarski(X12),X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,k2_relat_1(esk6_0),X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk6_0) = k2_tarski(esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1)),k1_relat_1(esk6_0))
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_3(esk6_0,k2_relat_1(esk6_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_19]),c_0_20])])).

cnf(c_0_35,negated_conjecture,
    ( X1 = esk5_0
    | ~ r1_tarski(k2_tarski(X1,X1),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_tarski(esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1)),esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1))),k1_relat_1(esk6_0))
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X18,X19] : r1_tarski(k1_tarski(X18),k2_tarski(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1))) = esk1_2(k2_relat_1(esk6_0),X1)
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1)) = esk5_0
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k9_relat_1(X22,k1_relat_1(X22)) = k2_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ( ~ r1_tarski(X16,k1_tarski(X17))
        | X16 = k1_xboole_0
        | X16 = k1_tarski(X17) )
      & ( X16 != k1_xboole_0
        | r1_tarski(X16,k1_tarski(X17)) )
      & ( X16 != k1_tarski(X17)
        | r1_tarski(X16,k1_tarski(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( esk1_2(k2_relat_1(esk6_0),X1) = k1_funct_1(esk6_0,esk5_0)
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_24])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_24])).

fof(c_0_48,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(k1_tarski(X14),X15)
      | ~ r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( ( k9_relat_1(X24,X23) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_xboole_0(k1_relat_1(X24),X23)
        | k9_relat_1(X24,X23) = k1_xboole_0
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_50,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),X1)
    | ~ r2_hidden(k1_funct_1(esk6_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_relat_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | ~ r1_tarski(X1,k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_24]),c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_tarski(k1_funct_1(esk6_0,esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk6_0) != k2_tarski(k1_funct_1(esk6_0,esk5_0),k1_funct_1(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_24])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_24])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk6_0))
    | k2_relat_1(esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20])])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_31])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk6_0),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.43  # and selection function PSelectComplexPreferEQ.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.43  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.20/0.43  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.20/0.43  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.20/0.43  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.43  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.20/0.43  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.20/0.43  fof(c_0_11, plain, ![X25, X26, X27, X29, X30, X31, X33]:((((r2_hidden(esk2_3(X25,X26,X27),k1_relat_1(X25))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X27=k1_funct_1(X25,esk2_3(X25,X26,X27))|~r2_hidden(X27,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(~r2_hidden(X30,k1_relat_1(X25))|X29!=k1_funct_1(X25,X30)|r2_hidden(X29,X26)|X26!=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&((~r2_hidden(esk3_2(X25,X31),X31)|(~r2_hidden(X33,k1_relat_1(X25))|esk3_2(X25,X31)!=k1_funct_1(X25,X33))|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&((r2_hidden(esk4_2(X25,X31),k1_relat_1(X25))|r2_hidden(esk3_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(esk3_2(X25,X31)=k1_funct_1(X25,esk4_2(X25,X31))|r2_hidden(esk3_2(X25,X31),X31)|X31=k2_relat_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.43  fof(c_0_12, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.20/0.43  cnf(c_0_13, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(k1_relat_1(esk6_0)=k1_tarski(esk5_0)&k2_relat_1(esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.43  fof(c_0_15, plain, ![X20, X21]:(~r1_tarski(k1_tarski(X20),k1_tarski(X21))|X20=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.20/0.43  fof(c_0_16, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  fof(c_0_17, plain, ![X12, X13]:((~r1_tarski(k1_tarski(X12),X13)|r2_hidden(X12,X13))&(~r2_hidden(X12,X13)|r1_tarski(k1_tarski(X12),X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.43  cnf(c_0_18, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  fof(c_0_21, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  cnf(c_0_22, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_23, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_25, negated_conjecture, (k1_relat_1(esk6_0)=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_26, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_3(esk6_0,k2_relat_1(esk6_0),X1),k1_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.20/0.43  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_29, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_30, plain, (X1=X2|~r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk6_0)=k2_tarski(esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.20/0.43  cnf(c_0_32, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.43  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1)),k1_relat_1(esk6_0))|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.43  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk6_0,esk2_3(esk6_0,k2_relat_1(esk6_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_19]), c_0_20])])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (X1=esk5_0|~r1_tarski(k2_tarski(X1,X1),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.43  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_tarski(esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1)),esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1))),k1_relat_1(esk6_0))|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.43  fof(c_0_37, plain, ![X18, X19]:r1_tarski(k1_tarski(X18),k2_tarski(X18,X19)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk6_0,esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1)))=esk1_2(k2_relat_1(esk6_0),X1)|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (esk2_3(esk6_0,k2_relat_1(esk6_0),esk1_2(k2_relat_1(esk6_0),X1))=esk5_0|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.43  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_41, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.43  fof(c_0_42, plain, ![X22]:(~v1_relat_1(X22)|k9_relat_1(X22,k1_relat_1(X22))=k2_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.20/0.43  fof(c_0_43, plain, ![X16, X17]:((~r1_tarski(X16,k1_tarski(X17))|(X16=k1_xboole_0|X16=k1_tarski(X17)))&((X16!=k1_xboole_0|r1_tarski(X16,k1_tarski(X17)))&(X16!=k1_tarski(X17)|r1_tarski(X16,k1_tarski(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.43  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (esk1_2(k2_relat_1(esk6_0),X1)=k1_funct_1(esk6_0,esk5_0)|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.43  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_40, c_0_24])).
% 0.20/0.43  cnf(c_0_47, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_41, c_0_24])).
% 0.20/0.43  fof(c_0_48, plain, ![X14, X15]:(~r1_xboole_0(k1_tarski(X14),X15)|~r2_hidden(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.20/0.43  fof(c_0_49, plain, ![X23, X24]:((k9_relat_1(X24,X23)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_xboole_0(k1_relat_1(X24),X23)|k9_relat_1(X24,X23)=k1_xboole_0|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.20/0.43  cnf(c_0_50, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.43  cnf(c_0_51, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),X1)|~r2_hidden(k1_funct_1(esk6_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.43  cnf(c_0_53, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (k2_relat_1(esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_55, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.43  cnf(c_0_56, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (k9_relat_1(esk6_0,k1_relat_1(esk6_0))=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_50, c_0_20])).
% 0.20/0.43  cnf(c_0_58, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|~r1_tarski(X1,k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_24]), c_0_24])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_tarski(k1_funct_1(esk6_0,esk5_0),X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk6_0)!=k2_tarski(k1_funct_1(esk6_0,esk5_0),k1_funct_1(esk6_0,esk5_0))), inference(rw,[status(thm)],[c_0_54, c_0_24])).
% 0.20/0.43  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_55, c_0_24])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (r1_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk6_0))|k2_relat_1(esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_20])])).
% 0.20/0.43  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_0,X1)|~r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 0.20/0.43  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_31]), c_0_31])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk6_0),X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_31])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (r1_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 70
% 0.20/0.43  # Proof object clause steps            : 47
% 0.20/0.43  # Proof object formula steps           : 23
% 0.20/0.43  # Proof object conjectures             : 28
% 0.20/0.43  # Proof object clause conjectures      : 25
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 17
% 0.20/0.43  # Proof object initial formulas used   : 11
% 0.20/0.43  # Proof object generating inferences   : 19
% 0.20/0.43  # Proof object simplifying inferences  : 24
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 11
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 25
% 0.20/0.43  # Removed in clause preprocessing      : 1
% 0.20/0.43  # Initial clauses in saturation        : 24
% 0.20/0.43  # Processed clauses                    : 387
% 0.20/0.43  # ...of these trivial                  : 2
% 0.20/0.43  # ...subsumed                          : 146
% 0.20/0.43  # ...remaining for further processing  : 239
% 0.20/0.43  # Other redundant clauses eliminated   : 32
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 35
% 0.20/0.43  # Backward-rewritten                   : 117
% 0.20/0.43  # Generated clauses                    : 2311
% 0.20/0.43  # ...of the previous two non-trivial   : 2162
% 0.20/0.43  # Contextual simplify-reflections      : 4
% 0.20/0.43  # Paramodulations                      : 2259
% 0.20/0.43  # Factorizations                       : 19
% 0.20/0.43  # Equation resolutions                 : 34
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 59
% 0.20/0.43  #    Positive orientable unit clauses  : 13
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 1
% 0.20/0.43  #    Non-unit-clauses                  : 45
% 0.20/0.43  # Current number of unprocessed clauses: 1413
% 0.20/0.43  # ...number of literals in the above   : 6051
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 176
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 2631
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 1420
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 176
% 0.20/0.43  # Unit Clause-clause subsumption calls : 111
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 25
% 0.20/0.43  # BW rewrite match successes           : 11
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 36389
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.077 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.084 s
% 0.20/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
