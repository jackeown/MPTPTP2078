%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0766+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 133 expanded)
%              Number of clauses        :   40 (  56 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  191 ( 802 expanded)
%              Number of equality atoms :   19 (  58 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => ? [X3] :
        ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,k3_relat_1(X1))
            & ~ r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t12_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & ? [X3] :
                  ( r2_hidden(X3,k3_relat_1(X1))
                  & ~ r2_hidden(k4_tarski(X3,X2),X1) )
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X1))
                    & r2_hidden(k4_tarski(X2,X3),X1)
                    & ! [X4] :
                        ~ ( r2_hidden(X4,k3_relat_1(X1))
                          & r2_hidden(k4_tarski(X2,X4),X1)
                          & X4 != X2
                          & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t10_wellord1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(c_0_10,plain,(
    ! [X13,X14,X16,X17] :
      ( ( r2_hidden(X16,k3_relat_1(X13))
        | ~ r2_hidden(X16,esk3_2(X13,X14))
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X16,X14),X13)
        | ~ r2_hidden(X16,esk3_2(X13,X14))
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X17,k3_relat_1(X13))
        | r2_hidden(k4_tarski(X17,X14),X13)
        | r2_hidden(X17,esk3_2(X13,X14))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e7_18__wellord1])])])])])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,esk3_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => ! [X2] :
              ~ ( r2_hidden(X2,k3_relat_1(X1))
                & ? [X3] :
                    ( r2_hidden(X3,k3_relat_1(X1))
                    & ~ r2_hidden(k4_tarski(X3,X2),X1) )
                & ! [X3] :
                    ~ ( r2_hidden(X3,k3_relat_1(X1))
                      & r2_hidden(k4_tarski(X2,X3),X1)
                      & ! [X4] :
                          ~ ( r2_hidden(X4,k3_relat_1(X1))
                            & r2_hidden(k4_tarski(X2,X4),X1)
                            & X4 != X2
                            & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_wellord1])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_16,plain,(
    ! [X11] : m1_subset_1(esk2_1(X11),X11) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_18,plain,(
    ! [X18,X19,X21] :
      ( ( r2_hidden(esk4_2(X18,X19),X19)
        | ~ r1_tarski(X19,k3_relat_1(X18))
        | X19 = k1_xboole_0
        | ~ v2_wellord1(X18)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X21,X19)
        | r2_hidden(k4_tarski(esk4_2(X18,X19),X21),X18)
        | ~ r1_tarski(X19,k3_relat_1(X18))
        | X19 = k1_xboole_0
        | ~ v2_wellord1(X18)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(esk3_2(X1,X2),X3),k3_relat_1(X1))
    | r1_tarski(esk3_2(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_21,negated_conjecture,(
    ! [X31] :
      ( v1_relat_1(esk5_0)
      & v2_wellord1(esk5_0)
      & r2_hidden(esk6_0,k3_relat_1(esk5_0))
      & r2_hidden(esk7_0,k3_relat_1(esk5_0))
      & ~ r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0)
      & ( r2_hidden(esk8_1(X31),k3_relat_1(esk5_0))
        | ~ r2_hidden(X31,k3_relat_1(esk5_0))
        | ~ r2_hidden(k4_tarski(esk6_0,X31),esk5_0) )
      & ( r2_hidden(k4_tarski(esk6_0,esk8_1(X31)),esk5_0)
        | ~ r2_hidden(X31,k3_relat_1(esk5_0))
        | ~ r2_hidden(k4_tarski(esk6_0,X31),esk5_0) )
      & ( esk8_1(X31) != esk6_0
        | ~ r2_hidden(X31,k3_relat_1(esk5_0))
        | ~ r2_hidden(k4_tarski(esk6_0,X31),esk5_0) )
      & ( ~ r2_hidden(k4_tarski(X31,esk8_1(X31)),esk5_0)
        | ~ r2_hidden(X31,k3_relat_1(esk5_0))
        | ~ r2_hidden(k4_tarski(esk6_0,X31),esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(esk3_2(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk4_2(X3,X2),X1),X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k3_relat_1(X3))
    | ~ v2_wellord1(X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | r2_hidden(X1,esk3_2(X2,X3))
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk8_1(X1)),esk5_0)
    | ~ r2_hidden(X1,k3_relat_1(esk5_0))
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X27] :
      ( ~ v1_xboole_0(X27)
      | X27 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk2_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,esk3_2(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | r2_hidden(esk4_2(X1,esk3_2(X1,X2)),esk3_2(X1,X2))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_2(X1,esk3_2(X1,X2)),X3),X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,esk3_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,X1),esk5_0)
    | r2_hidden(esk6_0,esk3_2(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( v2_wellord1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk8_1(X1)),esk5_0)
    | ~ r2_hidden(X1,k3_relat_1(esk5_0))
    | ~ r2_hidden(k4_tarski(esk6_0,X1),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk8_1(esk6_0)),esk5_0)
    | ~ r2_hidden(k4_tarski(esk6_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( v1_xboole_0(esk2_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,plain,
    ( esk3_2(X1,X2) = k1_xboole_0
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,esk3_2(X1,X2)),X2),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( esk3_2(esk5_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_2(esk5_0,esk3_2(esk5_0,X1)),esk6_0),esk5_0)
    | r2_hidden(k4_tarski(esk6_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_30])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_29]),c_0_41])).

cnf(c_0_48,plain,
    ( esk2_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,X1),esk5_0)
    | r2_hidden(esk7_0,esk3_2(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_44]),c_0_30])])).

cnf(c_0_50,negated_conjecture,
    ( esk3_2(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_39]),c_0_30])]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_53,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_56,c_0_57]),
    [proof]).

%------------------------------------------------------------------------------
