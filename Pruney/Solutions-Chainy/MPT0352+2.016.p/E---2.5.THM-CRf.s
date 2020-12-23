%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 176 expanded)
%              Number of clauses        :   45 (  72 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 ( 487 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t33_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_20,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X23,X24)
      | r1_tarski(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(esk5_0,esk6_0)
      | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) )
    & ( r1_tarski(esk5_0,esk6_0)
      | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    | r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(X58))
      | k3_subset_1(X58,X59) = k4_xboole_0(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_25,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ( ~ r2_hidden(X51,X50)
        | r1_tarski(X51,X49)
        | X50 != k1_zfmisc_1(X49) )
      & ( ~ r1_tarski(X52,X49)
        | r2_hidden(X52,X50)
        | X50 != k1_zfmisc_1(X49) )
      & ( ~ r2_hidden(esk3_2(X53,X54),X54)
        | ~ r1_tarski(esk3_2(X53,X54),X53)
        | X54 = k1_zfmisc_1(X53) )
      & ( r2_hidden(esk3_2(X53,X54),X54)
        | r1_tarski(esk3_2(X53,X54),X53)
        | X54 = k1_zfmisc_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_26,plain,(
    ! [X56,X57] :
      ( ( ~ m1_subset_1(X57,X56)
        | r2_hidden(X57,X56)
        | v1_xboole_0(X56) )
      & ( ~ r2_hidden(X57,X56)
        | m1_subset_1(X57,X56)
        | v1_xboole_0(X56) )
      & ( ~ m1_subset_1(X57,X56)
        | v1_xboole_0(X57)
        | ~ v1_xboole_0(X56) )
      & ( ~ v1_xboole_0(X57)
        | m1_subset_1(X57,X56)
        | ~ v1_xboole_0(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_27,plain,(
    ! [X60] : ~ v1_xboole_0(k1_zfmisc_1(X60)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))
    | r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | r1_tarski(k4_xboole_0(X26,X28),k4_xboole_0(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_37,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | r1_tarski(k4_xboole_0(X31,X30),k4_xboole_0(X31,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))
    | r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(X1,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))
    | ~ r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_30])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))
    | r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_29]),c_0_30])])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk6_0),k3_subset_1(esk4_0,esk5_0))
    | r1_tarski(esk5_0,esk6_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk4_0,esk6_0),k4_xboole_0(esk4_0,esk5_0))
    | ~ r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_34])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,esk6_0),k4_xboole_0(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_29]),c_0_34])]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk6_0),k3_subset_1(esk4_0,esk5_0))
    | r1_tarski(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

fof(c_0_51,plain,(
    ! [X18,X19,X20] :
      ( ( r1_tarski(X18,X19)
        | ~ r1_tarski(X18,k4_xboole_0(X19,X20)) )
      & ( r1_xboole_0(X18,X20)
        | ~ r1_tarski(X18,k4_xboole_0(X19,X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk6_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_53,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_54,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_55,plain,(
    ! [X39,X40] :
      ( v1_xboole_0(X40)
      | ~ r1_tarski(X40,X39)
      | ~ r1_xboole_0(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_29]),c_0_34])])).

fof(c_0_58,plain,(
    ! [X32,X33] : r1_tarski(k4_xboole_0(X32,X33),X32) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_59,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_60,plain,(
    ! [X25] : r1_tarski(k1_xboole_0,X25) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

fof(c_0_70,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_73,plain,(
    ! [X34,X35] : k2_xboole_0(X34,k4_xboole_0(X35,X34)) = k2_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

fof(c_0_76,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_77,plain,(
    ! [X41,X42] : r1_tarski(X41,k2_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,k4_xboole_0(esk5_0,esk6_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,plain,
    ( k2_xboole_0(esk5_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_83,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.013 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.13/0.37  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.13/0.37  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.13/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.37  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.37  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.13/0.37  fof(t33_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 0.13/0.37  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.13/0.37  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.13/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.13/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.37  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.13/0.37  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.37  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 0.13/0.37  fof(c_0_20, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|~r1_tarski(X23,X24)|r1_tarski(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.13/0.37  fof(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))&(r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.13/0.37  cnf(c_0_22, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (r1_tarski(esk5_0,esk6_0)|r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_24, plain, ![X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(X58))|k3_subset_1(X58,X59)=k4_xboole_0(X58,X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.13/0.37  fof(c_0_25, plain, ![X49, X50, X51, X52, X53, X54]:(((~r2_hidden(X51,X50)|r1_tarski(X51,X49)|X50!=k1_zfmisc_1(X49))&(~r1_tarski(X52,X49)|r2_hidden(X52,X50)|X50!=k1_zfmisc_1(X49)))&((~r2_hidden(esk3_2(X53,X54),X54)|~r1_tarski(esk3_2(X53,X54),X53)|X54=k1_zfmisc_1(X53))&(r2_hidden(esk3_2(X53,X54),X54)|r1_tarski(esk3_2(X53,X54),X53)|X54=k1_zfmisc_1(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.37  fof(c_0_26, plain, ![X56, X57]:(((~m1_subset_1(X57,X56)|r2_hidden(X57,X56)|v1_xboole_0(X56))&(~r2_hidden(X57,X56)|m1_subset_1(X57,X56)|v1_xboole_0(X56)))&((~m1_subset_1(X57,X56)|v1_xboole_0(X57)|~v1_xboole_0(X56))&(~v1_xboole_0(X57)|m1_subset_1(X57,X56)|~v1_xboole_0(X56)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.37  fof(c_0_27, plain, ![X60]:~v1_xboole_0(k1_zfmisc_1(X60)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))|r1_tarski(esk5_0,esk6_0)|~r1_tarski(X1,k3_subset_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.37  cnf(c_0_29, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_31, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|r1_tarski(k4_xboole_0(X26,X28),k4_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).
% 0.13/0.37  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_35, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)|~r1_tarski(k3_subset_1(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_37, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|r1_tarski(k4_xboole_0(X31,X30),k4_xboole_0(X31,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk4_0,esk5_0))|r1_tarski(esk5_0,esk6_0)|~r1_tarski(X1,k4_xboole_0(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.13/0.37  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (~r1_tarski(k4_xboole_0(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))|~r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_30])])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,esk6_0),k3_subset_1(esk4_0,esk5_0))|r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_29]), c_0_30])])).
% 0.13/0.37  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk6_0),k3_subset_1(esk4_0,esk5_0))|r1_tarski(esk5_0,esk6_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (~r1_tarski(k4_xboole_0(esk4_0,esk6_0),k4_xboole_0(esk4_0,esk5_0))|~r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_34])])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,esk6_0),k4_xboole_0(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_29]), c_0_34])]), c_0_44])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,esk6_0),k3_subset_1(esk4_0,esk5_0))|r1_tarski(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 0.13/0.37  fof(c_0_51, plain, ![X18, X19, X20]:((r1_tarski(X18,X19)|~r1_tarski(X18,k4_xboole_0(X19,X20)))&(r1_xboole_0(X18,X20)|~r1_tarski(X18,k4_xboole_0(X19,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,esk6_0),k3_subset_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.37  fof(c_0_53, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.37  fof(c_0_54, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  fof(c_0_55, plain, ![X39, X40]:(v1_xboole_0(X40)|(~r1_tarski(X40,X39)|~r1_xboole_0(X40,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.13/0.37  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_29]), c_0_34])])).
% 0.13/0.37  fof(c_0_58, plain, ![X32, X33]:r1_tarski(k4_xboole_0(X32,X33),X32), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.37  fof(c_0_59, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  fof(c_0_60, plain, ![X25]:r1_tarski(k1_xboole_0,X25), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.37  cnf(c_0_61, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.37  cnf(c_0_62, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.37  cnf(c_0_63, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.37  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.37  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.37  cnf(c_0_66, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.37  cnf(c_0_67, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.37  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.37  cnf(c_0_69, negated_conjecture, (v1_xboole_0(k4_xboole_0(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.13/0.37  fof(c_0_70, plain, ![X21]:k2_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.13/0.37  cnf(c_0_71, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.37  cnf(c_0_72, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.37  fof(c_0_73, plain, ![X34, X35]:k2_xboole_0(X34,k4_xboole_0(X35,X34))=k2_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.37  cnf(c_0_74, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.37  cnf(c_0_75, negated_conjecture, (k1_xboole_0=k4_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.37  fof(c_0_76, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.37  fof(c_0_77, plain, ![X41, X42]:r1_tarski(X41,k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.37  cnf(c_0_78, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.37  cnf(c_0_79, plain, (k2_xboole_0(X1,k4_xboole_0(esk5_0,esk6_0))=X1), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.37  cnf(c_0_80, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.37  cnf(c_0_81, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.13/0.37  cnf(c_0_82, plain, (k2_xboole_0(esk5_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.13/0.37  cnf(c_0_83, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_50]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 84
% 0.13/0.37  # Proof object clause steps            : 45
% 0.13/0.37  # Proof object formula steps           : 39
% 0.13/0.37  # Proof object conjectures             : 24
% 0.13/0.37  # Proof object clause conjectures      : 21
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 22
% 0.13/0.37  # Proof object initial formulas used   : 19
% 0.13/0.37  # Proof object generating inferences   : 19
% 0.13/0.37  # Proof object simplifying inferences  : 23
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 22
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 37
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 37
% 0.13/0.37  # Processed clauses                    : 332
% 0.13/0.37  # ...of these trivial                  : 9
% 0.13/0.37  # ...subsumed                          : 84
% 0.13/0.37  # ...remaining for further processing  : 239
% 0.13/0.37  # Other redundant clauses eliminated   : 4
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 18
% 0.13/0.37  # Backward-rewritten                   : 22
% 0.13/0.37  # Generated clauses                    : 1349
% 0.13/0.37  # ...of the previous two non-trivial   : 1090
% 0.13/0.37  # Contextual simplify-reflections      : 2
% 0.13/0.37  # Paramodulations                      : 1335
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 4
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 149
% 0.13/0.37  #    Positive orientable unit clauses  : 50
% 0.13/0.37  #    Positive unorientable unit clauses: 2
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 95
% 0.13/0.37  # Current number of unprocessed clauses: 828
% 0.13/0.37  # ...number of literals in the above   : 2109
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 86
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 5168
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 4280
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 93
% 0.13/0.37  # Unit Clause-clause subsumption calls : 356
% 0.13/0.37  # Rewrite failures with RHS unbound    : 6
% 0.13/0.37  # BW rewrite match attempts            : 142
% 0.13/0.37  # BW rewrite match successes           : 25
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 17066
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.030 s
% 0.13/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
