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
% DateTime   : Thu Dec  3 10:53:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 (1217 expanded)
%              Number of clauses        :   60 ( 545 expanded)
%              Number of leaves         :    9 ( 327 expanded)
%              Depth                    :   15
%              Number of atoms          :  250 (5608 expanded)
%              Number of equality atoms :   81 (1931 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

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

fof(t15_funct_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X22,X23,X24,X26] :
      ( ( r2_hidden(esk3_3(X18,X19,X20),k1_relat_1(X18))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 = k1_funct_1(X18,esk3_3(X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X23,k1_relat_1(X18))
        | X22 != k1_funct_1(X18,X23)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(esk4_2(X18,X24),X24)
        | ~ r2_hidden(X26,k1_relat_1(X18))
        | esk4_2(X18,X24) != k1_funct_1(X18,X26)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk5_2(X18,X24),k1_relat_1(X18))
        | r2_hidden(esk4_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( esk4_2(X18,X24) = k1_funct_1(X18,esk5_2(X18,X24))
        | r2_hidden(esk4_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X36] :
      ( ( esk8_0 != k1_xboole_0
        | esk9_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | esk9_0 != k1_relat_1(X36)
        | ~ r1_tarski(k2_relat_1(X36),esk8_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X31,X32] :
      ( ( v1_relat_1(esk7_2(X31,X32))
        | X31 = k1_xboole_0 )
      & ( v1_funct_1(esk7_2(X31,X32))
        | X31 = k1_xboole_0 )
      & ( k1_relat_1(esk7_2(X31,X32)) = X31
        | X31 = k1_xboole_0 )
      & ( k2_relat_1(esk7_2(X31,X32)) = k1_tarski(X32)
        | X31 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X28,X30] :
      ( v1_relat_1(esk6_1(X28))
      & v1_funct_1(esk6_1(X28))
      & k1_relat_1(esk6_1(X28)) = X28
      & ( ~ r2_hidden(X30,X28)
        | k1_funct_1(esk6_1(X28),X30) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

cnf(c_0_15,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk9_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_relat_1(esk7_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v1_relat_1(esk7_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( v1_funct_1(esk7_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_24,plain,
    ( k1_funct_1(esk6_1(X2),X1) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( v1_funct_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( v1_relat_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( k1_relat_1(esk6_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk7_2(X1,X2)) != esk9_0
    | ~ r1_tarski(k1_tarski(X2),esk8_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_33,plain,
    ( k1_relat_1(esk7_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_34,plain,(
    ! [X16,X17] :
      ( ( ~ r1_tarski(k1_tarski(X16),X17)
        | r2_hidden(X16,X17) )
      & ( ~ r2_hidden(X16,X17)
        | r1_tarski(k1_tarski(X16),X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk3_3(esk6_1(X2),k2_relat_1(esk6_1(X2)),X1),X2)
    | ~ r2_hidden(X1,k2_relat_1(esk6_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_28]),c_0_25]),c_0_26])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | ~ r1_tarski(k1_tarski(X1),esk8_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(k1_relat_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk6_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25]),c_0_26]),c_0_27]),c_0_38])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))
    | ~ r2_hidden(X2,k2_relat_1(esk6_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_25]),c_0_26])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_3(esk6_1(X1),k2_relat_1(esk6_1(X1)),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(esk6_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_25]),c_0_26])])).

fof(c_0_50,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,plain,
    ( esk1_2(k2_relat_1(esk6_1(X1)),X2) = k1_xboole_0
    | r1_tarski(k2_relat_1(esk6_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))
    | ~ r2_hidden(X2,k2_relat_1(esk6_1(k2_relat_1(esk6_1(X1))))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( esk2_1(k2_relat_1(esk6_1(X1))) = k1_xboole_0
    | k2_relat_1(esk6_1(X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_46])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( X1 = k1_tarski(X2)
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(esk6_1(X1)),X2)
    | ~ r2_hidden(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk8_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_54])).

cnf(c_0_61,plain,
    ( k2_relat_1(esk6_1(k2_relat_1(esk6_1(X1)))) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_46])).

cnf(c_0_62,plain,
    ( k2_relat_1(esk6_1(X1)) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_56])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_57])).

cnf(c_0_65,plain,
    ( k2_relat_1(esk6_1(X1)) = k1_tarski(X2)
    | ~ r2_hidden(X2,k2_relat_1(esk6_1(X1)))
    | ~ r2_hidden(k1_xboole_0,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_27]),c_0_25]),c_0_26]),c_0_57])]),c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_38])).

cnf(c_0_68,plain,
    ( k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk6_1(X1)) = k1_tarski(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_68]),c_0_57])])).

cnf(c_0_71,plain,
    ( r2_hidden(esk3_3(esk6_1(X1),k1_tarski(k1_xboole_0),X2),X1)
    | ~ r2_hidden(X2,k1_tarski(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_69]),c_0_69])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_69])).

cnf(c_0_73,plain,
    ( r2_hidden(esk3_3(esk6_1(k1_xboole_0),k1_tarski(k1_xboole_0),X1),X2)
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,plain,
    ( k2_relat_1(esk6_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_75,plain,
    ( esk3_3(esk6_1(k1_xboole_0),k1_tarski(k1_xboole_0),X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_74]),c_0_27]),c_0_25]),c_0_26]),c_0_57])])])).

cnf(c_0_77,plain,
    ( ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_75]),c_0_76])).

cnf(c_0_78,plain,
    ( $false ),
    inference(spm,[status(thm)],[c_0_77,c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.19/0.40  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.40  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.19/0.40  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.19/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.40  fof(c_0_9, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.19/0.40  fof(c_0_10, plain, ![X18, X19, X20, X22, X23, X24, X26]:((((r2_hidden(esk3_3(X18,X19,X20),k1_relat_1(X18))|~r2_hidden(X20,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(X20=k1_funct_1(X18,esk3_3(X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(~r2_hidden(X23,k1_relat_1(X18))|X22!=k1_funct_1(X18,X23)|r2_hidden(X22,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&((~r2_hidden(esk4_2(X18,X24),X24)|(~r2_hidden(X26,k1_relat_1(X18))|esk4_2(X18,X24)!=k1_funct_1(X18,X26))|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&((r2_hidden(esk5_2(X18,X24),k1_relat_1(X18))|r2_hidden(esk4_2(X18,X24),X24)|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(esk4_2(X18,X24)=k1_funct_1(X18,esk5_2(X18,X24))|r2_hidden(esk4_2(X18,X24),X24)|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.40  fof(c_0_11, negated_conjecture, ![X36]:((esk8_0!=k1_xboole_0|esk9_0=k1_xboole_0)&(~v1_relat_1(X36)|~v1_funct_1(X36)|(esk9_0!=k1_relat_1(X36)|~r1_tarski(k2_relat_1(X36),esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.19/0.40  fof(c_0_12, plain, ![X31, X32]:((((v1_relat_1(esk7_2(X31,X32))|X31=k1_xboole_0)&(v1_funct_1(esk7_2(X31,X32))|X31=k1_xboole_0))&(k1_relat_1(esk7_2(X31,X32))=X31|X31=k1_xboole_0))&(k2_relat_1(esk7_2(X31,X32))=k1_tarski(X32)|X31=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.19/0.40  cnf(c_0_13, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_14, plain, ![X28, X30]:(((v1_relat_1(esk6_1(X28))&v1_funct_1(esk6_1(X28)))&k1_relat_1(esk6_1(X28))=X28)&(~r2_hidden(X30,X28)|k1_funct_1(esk6_1(X28),X30)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.19/0.40  cnf(c_0_15, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.40  cnf(c_0_17, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_18, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk9_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_20, plain, (k2_relat_1(esk7_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_21, plain, (v1_relat_1(esk7_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_22, plain, (v1_funct_1(esk7_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_23, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).
% 0.19/0.40  cnf(c_0_24, plain, (k1_funct_1(esk6_1(X2),X1)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_25, plain, (v1_funct_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_26, plain, (v1_relat_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_27, plain, (k1_relat_1(esk6_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_28, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_30, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk7_2(X1,X2))!=esk9_0|~r1_tarski(k1_tarski(X2),esk8_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 0.19/0.40  cnf(c_0_33, plain, (k1_relat_1(esk7_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  fof(c_0_34, plain, ![X16, X17]:((~r1_tarski(k1_tarski(X16),X17)|r2_hidden(X16,X17))&(~r2_hidden(X16,X17)|r1_tarski(k1_tarski(X16),X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.40  cnf(c_0_35, plain, (r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])])).
% 0.19/0.40  cnf(c_0_36, plain, (X1=k1_xboole_0|~r2_hidden(esk3_3(esk6_1(X2),k2_relat_1(esk6_1(X2)),X1),X2)|~r2_hidden(X1,k2_relat_1(esk6_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_28]), c_0_25]), c_0_26])])).
% 0.19/0.40  cnf(c_0_37, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r1_tarski(k1_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (esk9_0=k1_xboole_0|~r1_tarski(k1_tarski(X1),esk8_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])])).
% 0.19/0.40  cnf(c_0_40, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  fof(c_0_41, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.40  cnf(c_0_42, plain, (r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(k1_relat_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.19/0.40  cnf(c_0_43, plain, (X1=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk6_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_25]), c_0_26]), c_0_27]), c_0_38])])).
% 0.19/0.40  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (esk9_0=k1_xboole_0|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_48, plain, (r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))|~r2_hidden(X2,k2_relat_1(esk6_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_27]), c_0_25]), c_0_26])])).
% 0.19/0.40  cnf(c_0_49, plain, (r2_hidden(esk3_3(esk6_1(X1),k2_relat_1(esk6_1(X1)),X2),X1)|~r2_hidden(X2,k2_relat_1(esk6_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_25]), c_0_26])])).
% 0.19/0.40  fof(c_0_50, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.40  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_53, plain, (esk1_2(k2_relat_1(esk6_1(X1)),X2)=k1_xboole_0|r1_tarski(k2_relat_1(esk6_1(X1)),X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (esk9_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.19/0.40  cnf(c_0_55, plain, (r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))|~r2_hidden(X2,k2_relat_1(esk6_1(k2_relat_1(esk6_1(X1)))))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.40  cnf(c_0_56, plain, (esk2_1(k2_relat_1(esk6_1(X1)))=k1_xboole_0|k2_relat_1(esk6_1(X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_46])).
% 0.19/0.40  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.40  cnf(c_0_58, plain, (X1=k1_tarski(X2)|~r2_hidden(X2,X1)|~r1_tarski(X1,k1_tarski(X2))), inference(spm,[status(thm)],[c_0_51, c_0_40])).
% 0.19/0.40  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(esk6_1(X1)),X2)|~r2_hidden(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk8_0)), inference(rw,[status(thm)],[c_0_19, c_0_54])).
% 0.19/0.40  cnf(c_0_61, plain, (k2_relat_1(esk6_1(k2_relat_1(esk6_1(X1))))=k1_xboole_0|r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))), inference(spm,[status(thm)],[c_0_55, c_0_46])).
% 0.19/0.40  cnf(c_0_62, plain, (k2_relat_1(esk6_1(X1))=k1_xboole_0|r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))), inference(spm,[status(thm)],[c_0_46, c_0_56])).
% 0.19/0.40  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_64, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_57])).
% 0.19/0.40  cnf(c_0_65, plain, (k2_relat_1(esk6_1(X1))=k1_tarski(X2)|~r2_hidden(X2,k2_relat_1(esk6_1(X1)))|~r2_hidden(k1_xboole_0,k1_tarski(X2))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (r2_hidden(k1_xboole_0,k2_relat_1(esk6_1(X1)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_27]), c_0_25]), c_0_26]), c_0_57])]), c_0_62])).
% 0.19/0.40  cnf(c_0_67, plain, (r2_hidden(X1,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_63, c_0_38])).
% 0.19/0.40  cnf(c_0_68, plain, (k1_tarski(X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_40])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk6_1(X1))=k1_tarski(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.19/0.40  cnf(c_0_70, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_68]), c_0_57])])).
% 0.19/0.40  cnf(c_0_71, plain, (r2_hidden(esk3_3(esk6_1(X1),k1_tarski(k1_xboole_0),X2),X1)|~r2_hidden(X2,k1_tarski(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_69]), c_0_69])).
% 0.19/0.40  cnf(c_0_72, plain, (X1=k1_xboole_0|~r2_hidden(X1,k1_tarski(k1_xboole_0))), inference(rw,[status(thm)],[c_0_43, c_0_69])).
% 0.19/0.40  cnf(c_0_73, plain, (r2_hidden(esk3_3(esk6_1(k1_xboole_0),k1_tarski(k1_xboole_0),X1),X2)|~r2_hidden(X1,k1_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.40  cnf(c_0_74, plain, (k2_relat_1(esk6_1(X1))=k1_xboole_0|~r2_hidden(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 0.19/0.40  cnf(c_0_75, plain, (esk3_3(esk6_1(k1_xboole_0),k1_tarski(k1_xboole_0),X1)=k1_xboole_0|~r2_hidden(X1,k1_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (~r2_hidden(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_74]), c_0_27]), c_0_25]), c_0_26]), c_0_57])])])).
% 0.19/0.40  cnf(c_0_77, plain, (~r2_hidden(X1,k1_tarski(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_75]), c_0_76])).
% 0.19/0.40  cnf(c_0_78, plain, ($false), inference(spm,[status(thm)],[c_0_77, c_0_67]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 79
% 0.19/0.40  # Proof object clause steps            : 60
% 0.19/0.40  # Proof object formula steps           : 19
% 0.19/0.40  # Proof object conjectures             : 13
% 0.19/0.40  # Proof object clause conjectures      : 10
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 22
% 0.19/0.40  # Proof object initial formulas used   : 9
% 0.19/0.40  # Proof object generating inferences   : 31
% 0.19/0.40  # Proof object simplifying inferences  : 48
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 9
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 26
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 26
% 0.19/0.40  # Processed clauses                    : 344
% 0.19/0.40  # ...of these trivial                  : 3
% 0.19/0.40  # ...subsumed                          : 164
% 0.19/0.40  # ...remaining for further processing  : 177
% 0.19/0.40  # Other redundant clauses eliminated   : 11
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 33
% 0.19/0.40  # Backward-rewritten                   : 38
% 0.19/0.40  # Generated clauses                    : 1042
% 0.19/0.40  # ...of the previous two non-trivial   : 847
% 0.19/0.40  # Contextual simplify-reflections      : 16
% 0.19/0.40  # Paramodulations                      : 1031
% 0.19/0.40  # Factorizations                       : 1
% 0.19/0.40  # Equation resolutions                 : 11
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 76
% 0.19/0.40  #    Positive orientable unit clauses  : 8
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 4
% 0.19/0.40  #    Non-unit-clauses                  : 64
% 0.19/0.40  # Current number of unprocessed clauses: 470
% 0.19/0.40  # ...number of literals in the above   : 2013
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 96
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1892
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1262
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 138
% 0.19/0.40  # Unit Clause-clause subsumption calls : 161
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 86
% 0.19/0.40  # BW rewrite match successes           : 20
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 18671
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.053 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.058 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
