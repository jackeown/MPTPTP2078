%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 353 expanded)
%              Number of clauses        :   41 ( 160 expanded)
%              Number of leaves         :    8 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 (1323 expanded)
%              Number of equality atoms :   32 ( 223 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t65_subset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X3)
        & r1_tarski(X3,k2_zfmisc_1(X1,X2))
        & ! [X5] :
            ( m1_subset_1(X5,X1)
           => ! [X6] :
                ( m1_subset_1(X6,X2)
               => X4 != k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
       => ~ ( r2_hidden(X1,X4)
            & ! [X5,X6] :
                ~ ( X1 = k4_tarski(X5,X6)
                  & r2_hidden(X5,X2)
                  & r2_hidden(X6,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_relset_1])).

fof(c_0_9,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X39,X40)
      | v1_xboole_0(X40)
      | r2_hidden(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_10,plain,(
    ! [X33,X34,X35,X36] :
      ( ( m1_subset_1(esk8_4(X33,X34,X35,X36),X33)
        | ~ r2_hidden(X36,X35)
        | ~ r1_tarski(X35,k2_zfmisc_1(X33,X34)) )
      & ( m1_subset_1(esk9_4(X33,X34,X35,X36),X34)
        | ~ r2_hidden(X36,X35)
        | ~ r1_tarski(X35,k2_zfmisc_1(X33,X34)) )
      & ( X36 = k4_tarski(esk8_4(X33,X34,X35,X36),esk9_4(X33,X34,X35,X36))
        | ~ r2_hidden(X36,X35)
        | ~ r1_tarski(X35,k2_zfmisc_1(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_subset_1])])])])).

fof(c_0_11,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X41,k1_zfmisc_1(X42))
        | r1_tarski(X41,X42) )
      & ( ~ r1_tarski(X41,X42)
        | m1_subset_1(X41,k1_zfmisc_1(X42)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,(
    ! [X47,X48] :
      ( m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))
      & r2_hidden(esk10_0,esk13_0)
      & ( esk10_0 != k4_tarski(X47,X48)
        | ~ r2_hidden(X47,esk11_0)
        | ~ r2_hidden(X48,esk12_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_13,plain,(
    ! [X16,X17,X18,X19,X22,X23,X24,X25,X26,X27,X29,X30] :
      ( ( r2_hidden(esk3_4(X16,X17,X18,X19),X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk4_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( X19 = k4_tarski(esk3_4(X16,X17,X18,X19),esk4_4(X16,X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( ~ r2_hidden(X23,X16)
        | ~ r2_hidden(X24,X17)
        | X22 != k4_tarski(X23,X24)
        | r2_hidden(X22,X18)
        | X18 != k2_zfmisc_1(X16,X17) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | ~ r2_hidden(X29,X25)
        | ~ r2_hidden(X30,X26)
        | esk5_3(X25,X26,X27) != k4_tarski(X29,X30)
        | X27 = k2_zfmisc_1(X25,X26) )
      & ( r2_hidden(esk6_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_zfmisc_1(X25,X26) )
      & ( r2_hidden(esk7_3(X25,X26,X27),X26)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_zfmisc_1(X25,X26) )
      & ( esk5_3(X25,X26,X27) = k4_tarski(esk6_3(X25,X26,X27),esk7_3(X25,X26,X27))
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k2_zfmisc_1(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk9_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk9_4(X1,X2,X3,X4),X2)
    | v1_xboole_0(X2)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk13_0,k2_zfmisc_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk8_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ( r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X13)
        | ~ r2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | ~ r2_xboole_0(X11,X12) )
      & ( X11 != X12
        | ~ r2_xboole_0(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | X11 = X12
        | r2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( esk10_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X2,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( X1 = k4_tarski(esk8_4(X2,X3,X4,X1),esk9_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_4(esk11_0,esk12_0,esk13_0,X1),esk12_0)
    | v1_xboole_0(esk12_0)
    | ~ r2_hidden(X1,esk13_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk10_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( r2_hidden(esk8_4(X1,X2,X3,X4),X1)
    | v1_xboole_0(X1)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk9_4(X2,X3,X1,esk10_0),esk12_0)
    | ~ r2_hidden(esk8_4(X2,X3,X1,esk10_0),esk11_0)
    | ~ r2_hidden(esk10_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk9_4(esk11_0,esk12_0,esk13_0,esk10_0),esk12_0)
    | v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk8_4(esk11_0,esk12_0,esk13_0,X1),esk11_0)
    | v1_xboole_0(esk11_0)
    | ~ r2_hidden(X1,esk13_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_40,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = esk13_0
    | r2_xboole_0(esk13_0,k2_zfmisc_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,plain,
    ( ~ r2_xboole_0(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(esk12_0)
    | ~ r2_hidden(esk8_4(esk11_0,esk12_0,esk13_0,esk10_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),c_0_31])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk8_4(esk11_0,esk12_0,esk13_0,esk10_0),esk11_0)
    | v1_xboole_0(esk11_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = esk13_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk11_0,esk12_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = esk13_0
    | ~ v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk11_0)
    | v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = esk13_0
    | ~ v1_xboole_0(esk11_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(esk11_0,esk12_0) = esk13_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(esk13_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_54,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_50,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t6_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 0.19/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.39  fof(t65_subset_1, axiom, ![X1, X2, X3, X4]:~(((r2_hidden(X4,X3)&r1_tarski(X3,k2_zfmisc_1(X1,X2)))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>X4!=k4_tarski(X5,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 0.19/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.39  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.39  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.19/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3))))))), inference(assume_negation,[status(cth)],[t6_relset_1])).
% 0.19/0.39  fof(c_0_9, plain, ![X39, X40]:(~m1_subset_1(X39,X40)|(v1_xboole_0(X40)|r2_hidden(X39,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.39  fof(c_0_10, plain, ![X33, X34, X35, X36]:((m1_subset_1(esk8_4(X33,X34,X35,X36),X33)|(~r2_hidden(X36,X35)|~r1_tarski(X35,k2_zfmisc_1(X33,X34))))&((m1_subset_1(esk9_4(X33,X34,X35,X36),X34)|(~r2_hidden(X36,X35)|~r1_tarski(X35,k2_zfmisc_1(X33,X34))))&(X36=k4_tarski(esk8_4(X33,X34,X35,X36),esk9_4(X33,X34,X35,X36))|(~r2_hidden(X36,X35)|~r1_tarski(X35,k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_subset_1])])])])).
% 0.19/0.39  fof(c_0_11, plain, ![X41, X42]:((~m1_subset_1(X41,k1_zfmisc_1(X42))|r1_tarski(X41,X42))&(~r1_tarski(X41,X42)|m1_subset_1(X41,k1_zfmisc_1(X42)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.39  fof(c_0_12, negated_conjecture, ![X47, X48]:(m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))&(r2_hidden(esk10_0,esk13_0)&(esk10_0!=k4_tarski(X47,X48)|~r2_hidden(X47,esk11_0)|~r2_hidden(X48,esk12_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.19/0.39  fof(c_0_13, plain, ![X16, X17, X18, X19, X22, X23, X24, X25, X26, X27, X29, X30]:(((((r2_hidden(esk3_4(X16,X17,X18,X19),X16)|~r2_hidden(X19,X18)|X18!=k2_zfmisc_1(X16,X17))&(r2_hidden(esk4_4(X16,X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k2_zfmisc_1(X16,X17)))&(X19=k4_tarski(esk3_4(X16,X17,X18,X19),esk4_4(X16,X17,X18,X19))|~r2_hidden(X19,X18)|X18!=k2_zfmisc_1(X16,X17)))&(~r2_hidden(X23,X16)|~r2_hidden(X24,X17)|X22!=k4_tarski(X23,X24)|r2_hidden(X22,X18)|X18!=k2_zfmisc_1(X16,X17)))&((~r2_hidden(esk5_3(X25,X26,X27),X27)|(~r2_hidden(X29,X25)|~r2_hidden(X30,X26)|esk5_3(X25,X26,X27)!=k4_tarski(X29,X30))|X27=k2_zfmisc_1(X25,X26))&(((r2_hidden(esk6_3(X25,X26,X27),X25)|r2_hidden(esk5_3(X25,X26,X27),X27)|X27=k2_zfmisc_1(X25,X26))&(r2_hidden(esk7_3(X25,X26,X27),X26)|r2_hidden(esk5_3(X25,X26,X27),X27)|X27=k2_zfmisc_1(X25,X26)))&(esk5_3(X25,X26,X27)=k4_tarski(esk6_3(X25,X26,X27),esk7_3(X25,X26,X27))|r2_hidden(esk5_3(X25,X26,X27),X27)|X27=k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.39  cnf(c_0_14, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_15, plain, (m1_subset_1(esk9_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk13_0,k1_zfmisc_1(k2_zfmisc_1(esk11_0,esk12_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  fof(c_0_18, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  cnf(c_0_19, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_20, plain, (r2_hidden(esk9_4(X1,X2,X3,X4),X2)|v1_xboole_0(X2)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (r1_tarski(esk13_0,k2_zfmisc_1(esk11_0,esk12_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.39  cnf(c_0_22, plain, (m1_subset_1(esk8_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  fof(c_0_23, plain, ![X13, X14]:((r2_hidden(esk2_2(X13,X14),X14)|~r2_xboole_0(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X13)|~r2_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.19/0.39  fof(c_0_24, plain, ![X11, X12]:(((r1_tarski(X11,X12)|~r2_xboole_0(X11,X12))&(X11!=X12|~r2_xboole_0(X11,X12)))&(~r1_tarski(X11,X12)|X11=X12|r2_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.39  cnf(c_0_25, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_26, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_27, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (esk10_0!=k4_tarski(X1,X2)|~r2_hidden(X1,esk11_0)|~r2_hidden(X2,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_29, plain, (X1=k4_tarski(esk8_4(X2,X3,X4,X1),esk9_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~r1_tarski(X4,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_4(esk11_0,esk12_0,esk13_0,X1),esk12_0)|v1_xboole_0(esk12_0)|~r2_hidden(X1,esk13_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk10_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_32, plain, (r2_hidden(esk8_4(X1,X2,X3,X4),X1)|v1_xboole_0(X1)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_14, c_0_22])).
% 0.19/0.39  cnf(c_0_33, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_34, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_35, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_36, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(esk9_4(X2,X3,X1,esk10_0),esk12_0)|~r2_hidden(esk8_4(X2,X3,X1,esk10_0),esk11_0)|~r2_hidden(esk10_0,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29])])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(esk9_4(esk11_0,esk12_0,esk13_0,esk10_0),esk12_0)|v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(esk8_4(esk11_0,esk12_0,esk13_0,X1),esk11_0)|v1_xboole_0(esk11_0)|~r2_hidden(X1,esk13_0)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.19/0.39  cnf(c_0_40, plain, (~r2_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_26, c_0_33])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=esk13_0|r2_xboole_0(esk13_0,k2_zfmisc_1(esk11_0,esk12_0))), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.19/0.39  cnf(c_0_42, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_26, c_0_35])).
% 0.19/0.39  cnf(c_0_43, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_44, plain, (~r2_xboole_0(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_36, c_0_33])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (v1_xboole_0(esk12_0)|~r2_hidden(esk8_4(esk11_0,esk12_0,esk13_0,esk10_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_21]), c_0_31])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(esk8_4(esk11_0,esk12_0,esk13_0,esk10_0),esk11_0)|v1_xboole_0(esk11_0)), inference(spm,[status(thm)],[c_0_39, c_0_31])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=esk13_0|~v1_xboole_0(k2_zfmisc_1(esk11_0,esk12_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_48, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=esk13_0|~v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk11_0)|v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=esk13_0|~v1_xboole_0(esk11_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(esk11_0,esk12_0)=esk13_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(esk13_0)), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 0.19/0.39  cnf(c_0_54, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_52]), c_0_53])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (~v1_xboole_0(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_53])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_50, c_0_55]), c_0_56]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 58
% 0.19/0.39  # Proof object clause steps            : 41
% 0.19/0.39  # Proof object formula steps           : 17
% 0.19/0.39  # Proof object conjectures             : 23
% 0.19/0.39  # Proof object clause conjectures      : 20
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 14
% 0.19/0.39  # Proof object initial formulas used   : 8
% 0.19/0.39  # Proof object generating inferences   : 24
% 0.19/0.39  # Proof object simplifying inferences  : 11
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 8
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 24
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 24
% 0.19/0.39  # Processed clauses                    : 276
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 76
% 0.19/0.39  # ...remaining for further processing  : 199
% 0.19/0.39  # Other redundant clauses eliminated   : 8
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 8
% 0.19/0.39  # Generated clauses                    : 1000
% 0.19/0.39  # ...of the previous two non-trivial   : 994
% 0.19/0.39  # Contextual simplify-reflections      : 2
% 0.19/0.39  # Paramodulations                      : 988
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 8
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 156
% 0.19/0.39  #    Positive orientable unit clauses  : 2
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 4
% 0.19/0.39  #    Non-unit-clauses                  : 150
% 0.19/0.39  # Current number of unprocessed clauses: 766
% 0.19/0.39  # ...number of literals in the above   : 2218
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 38
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 3669
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 3010
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 78
% 0.19/0.39  # Unit Clause-clause subsumption calls : 139
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 1
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 15936
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.050 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.054 s
% 0.19/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
