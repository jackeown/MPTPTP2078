%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0764+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:09 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 262 expanded)
%              Number of clauses        :   43 (  98 expanded)
%              Number of leaves         :   11 (  64 expanded)
%              Depth                    :   22
%              Number of atoms          :  334 (1463 expanded)
%              Number of equality atoms :   42 ( 170 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t10_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(d2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r1_xboole_0(k1_wellord1(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(c_0_11,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | m1_subset_1(X37,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => ! [X2] :
              ~ ( r1_tarski(X2,k3_relat_1(X1))
                & X2 != k1_xboole_0
                & ! [X3] :
                    ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( r2_hidden(X4,X2)
                         => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_wellord1])).

fof(c_0_14,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,(
    ! [X45] :
      ( v1_relat_1(esk8_0)
      & v2_wellord1(esk8_0)
      & r1_tarski(esk9_0,k3_relat_1(esk8_0))
      & esk9_0 != k1_xboole_0
      & ( r2_hidden(esk10_1(X45),esk9_0)
        | ~ r2_hidden(X45,esk9_0) )
      & ( ~ r2_hidden(k4_tarski(X45,esk10_1(X45)),esk8_0)
        | ~ r2_hidden(X45,esk9_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk9_0,k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v6_relat_2(X22)
        | ~ r2_hidden(X23,k3_relat_1(X22))
        | ~ r2_hidden(X24,k3_relat_1(X22))
        | X23 = X24
        | r2_hidden(k4_tarski(X23,X24),X22)
        | r2_hidden(k4_tarski(X24,X23),X22)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk5_1(X22),k3_relat_1(X22))
        | v6_relat_2(X22)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk6_1(X22),k3_relat_1(X22))
        | v6_relat_2(X22)
        | ~ v1_relat_1(X22) )
      & ( esk5_1(X22) != esk6_1(X22)
        | v6_relat_2(X22)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk5_1(X22),esk6_1(X22)),X22)
        | v6_relat_2(X22)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk6_1(X22),esk5_1(X22)),X22)
        | v6_relat_2(X22)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,k3_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(k3_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_30,plain,(
    ! [X18] :
      ( ( v1_relat_2(X18)
        | ~ v2_wellord1(X18)
        | ~ v1_relat_1(X18) )
      & ( v8_relat_2(X18)
        | ~ v2_wellord1(X18)
        | ~ v1_relat_1(X18) )
      & ( v4_relat_2(X18)
        | ~ v2_wellord1(X18)
        | ~ v1_relat_1(X18) )
      & ( v6_relat_2(X18)
        | ~ v2_wellord1(X18)
        | ~ v1_relat_1(X18) )
      & ( v1_wellord1(X18)
        | ~ v2_wellord1(X18)
        | ~ v1_relat_1(X18) )
      & ( ~ v1_relat_2(X18)
        | ~ v8_relat_2(X18)
        | ~ v4_relat_2(X18)
        | ~ v6_relat_2(X18)
        | ~ v1_wellord1(X18)
        | v2_wellord1(X18)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_31,negated_conjecture,
    ( X1 = X2
    | r2_hidden(k4_tarski(X2,X1),esk8_0)
    | r2_hidden(k4_tarski(X1,X2),esk8_0)
    | ~ v6_relat_2(esk8_0)
    | ~ r2_hidden(X1,k3_relat_1(esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_32,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( v2_wellord1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( X1 = X2
    | r2_hidden(k4_tarski(X1,X2),esk8_0)
    | r2_hidden(k4_tarski(X2,X1),esk8_0)
    | ~ r2_hidden(X1,k3_relat_1(esk8_0))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_29])])).

fof(c_0_35,plain,(
    ! [X13,X14,X17] :
      ( ( r2_hidden(esk2_2(X13,X14),X14)
        | ~ r1_tarski(X14,k3_relat_1(X13))
        | X14 = k1_xboole_0
        | ~ v1_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( r1_xboole_0(k1_wellord1(X13,esk2_2(X13,X14)),X14)
        | ~ r1_tarski(X14,k3_relat_1(X13))
        | X14 = k1_xboole_0
        | ~ v1_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( r1_tarski(esk3_1(X13),k3_relat_1(X13))
        | v1_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( esk3_1(X13) != k1_xboole_0
        | v1_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X17,esk3_1(X13))
        | ~ r1_xboole_0(k1_wellord1(X13,X17),esk3_1(X13))
        | v1_wellord1(X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord1])])])])])).

cnf(c_0_36,negated_conjecture,
    ( X1 = X2
    | r2_hidden(k4_tarski(X2,X1),esk8_0)
    | r2_hidden(k4_tarski(X1,X2),esk8_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( X1 = esk2_2(X2,esk9_0)
    | r2_hidden(k4_tarski(X1,esk2_2(X2,esk9_0)),esk8_0)
    | r2_hidden(k4_tarski(esk2_2(X2,esk9_0),X1),esk8_0)
    | ~ r1_tarski(esk9_0,k3_relat_1(X2))
    | ~ v1_wellord1(X2)
    | ~ r2_hidden(X1,esk9_0)
    | ~ v1_relat_1(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk2_2(esk8_0,esk9_0),X1),esk8_0)
    | r2_hidden(k4_tarski(X1,esk2_2(esk8_0,esk9_0)),esk8_0)
    | ~ v1_wellord1(esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_29])])).

cnf(c_0_41,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != X6
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(X8,X6),X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( X9 = X6
        | ~ r2_hidden(k4_tarski(X9,X6),X5)
        | r2_hidden(X9,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | esk1_3(X5,X10,X11) = X10
        | ~ r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( esk1_3(X5,X10,X11) != X10
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( X1 = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(X1,esk2_2(esk8_0,esk9_0)),esk8_0)
    | r2_hidden(k4_tarski(esk2_2(esk8_0,esk9_0),X1),esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk10_1(X1),esk9_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( esk10_1(X1) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk2_2(esk8_0,esk9_0),esk10_1(X1)),esk8_0)
    | r2_hidden(k4_tarski(esk10_1(X1),esk2_2(esk8_0,esk9_0)),esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_47,plain,(
    ! [X31,X32,X34,X35,X36] :
      ( ( r2_hidden(esk7_2(X31,X32),X31)
        | r1_xboole_0(X31,X32) )
      & ( r2_hidden(esk7_2(X31,X32),X32)
        | r1_xboole_0(X31,X32) )
      & ( ~ r2_hidden(X36,X34)
        | ~ r2_hidden(X36,X35)
        | ~ r1_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_48,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( esk10_1(esk2_2(X1,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk10_1(esk2_2(X1,esk9_0)),esk2_2(esk8_0,esk9_0)),esk8_0)
    | r2_hidden(k4_tarski(esk2_2(esk8_0,esk9_0),esk10_1(esk2_2(X1,esk9_0))),esk8_0)
    | ~ r1_tarski(esk9_0,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_37]),c_0_38])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk2_2(X1,X2)),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk10_1(X1)),esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( esk10_1(esk2_2(X1,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk2_2(esk8_0,esk9_0),esk10_1(esk2_2(X1,esk9_0))),esk8_0)
    | r2_hidden(esk10_1(esk2_2(X1,esk9_0)),k1_wellord1(esk8_0,esk2_2(esk8_0,esk9_0)))
    | ~ r1_tarski(esk9_0,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29])])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_wellord1(X2)
    | ~ r2_hidden(X3,k1_wellord1(X2,esk2_2(X2,X1)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk10_1(esk2_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(esk10_1(esk2_2(esk8_0,esk9_0)),k1_wellord1(esk8_0,esk2_2(esk8_0,esk9_0)))
    | ~ v1_wellord1(esk8_0)
    | ~ r2_hidden(esk2_2(esk8_0,esk9_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_21]),c_0_29])])).

cnf(c_0_56,negated_conjecture,
    ( esk10_1(esk2_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | ~ v1_wellord1(esk8_0)
    | ~ r2_hidden(esk2_2(esk8_0,esk9_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_21]),c_0_29])]),c_0_38]),c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( esk10_1(esk2_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | ~ v1_wellord1(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_21]),c_0_29])]),c_0_38])).

fof(c_0_58,plain,(
    ! [X19,X20] :
      ( ( ~ v1_relat_2(X19)
        | ~ r2_hidden(X20,k3_relat_1(X19))
        | r2_hidden(k4_tarski(X20,X20),X19)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk4_1(X19),k3_relat_1(X19))
        | v1_relat_2(X19)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X19),esk4_1(X19)),X19)
        | v1_relat_2(X19)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_wellord1(esk8_0)
    | ~ r2_hidden(k4_tarski(esk2_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)
    | ~ r2_hidden(esk2_2(esk8_0,esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_relat_2(esk8_0)
    | ~ v1_wellord1(esk8_0)
    | ~ r2_hidden(esk2_2(esk8_0,esk9_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_29])]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_relat_2(esk8_0)
    | ~ v1_wellord1(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_37]),c_0_21]),c_0_29])]),c_0_38])).

cnf(c_0_63,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_wellord1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_33]),c_0_29])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_41]),c_0_33]),c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
