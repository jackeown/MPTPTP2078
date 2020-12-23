%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0365+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:30 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 105 expanded)
%              Number of clauses        :   38 (  48 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  183 ( 414 expanded)
%              Number of equality atoms :   31 (  70 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ( r1_xboole_0(X2,X3)
              & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ( r1_xboole_0(X2,X3)
                & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_subset_1])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))
    & r1_xboole_0(esk6_0,esk7_0)
    & r1_xboole_0(k3_subset_1(esk5_0,esk6_0),k3_subset_1(esk5_0,esk7_0))
    & esk6_0 != k3_subset_1(esk5_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X15,X14)
        | r2_hidden(X15,X14)
        | v1_xboole_0(X14) )
      & ( ~ r2_hidden(X15,X14)
        | m1_subset_1(X15,X14)
        | v1_xboole_0(X14) )
      & ( ~ m1_subset_1(X15,X14)
        | v1_xboole_0(X15)
        | ~ v1_xboole_0(X14) )
      & ( ~ v1_xboole_0(X15)
        | m1_subset_1(X15,X14)
        | ~ v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_13,plain,(
    ! [X33] : ~ v1_xboole_0(k1_zfmisc_1(X33)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_14,plain,(
    ! [X38,X39,X41,X42,X43] :
      ( ( r2_hidden(esk4_2(X38,X39),X38)
        | r1_xboole_0(X38,X39) )
      & ( r2_hidden(esk4_2(X38,X39),X39)
        | r1_xboole_0(X38,X39) )
      & ( ~ r2_hidden(X43,X41)
        | ~ r2_hidden(X43,X42)
        | ~ r1_xboole_0(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk5_0,esk6_0),k3_subset_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X7)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r1_tarski(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | ~ r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk5_0,esk6_0),k4_xboole_0(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_24,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( r2_hidden(X27,X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X28,X24)
        | r2_hidden(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk3_3(X29,X30,X31),X31)
        | ~ r2_hidden(esk3_3(X29,X30,X31),X29)
        | r2_hidden(esk3_3(X29,X30,X31),X30)
        | X31 = k4_xboole_0(X29,X30) )
      & ( r2_hidden(esk3_3(X29,X30,X31),X29)
        | r2_hidden(esk3_3(X29,X30,X31),X31)
        | X31 = k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk3_3(X29,X30,X31),X30)
        | r2_hidden(esk3_3(X29,X30,X31),X31)
        | X31 = k4_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk7_0))
    | ~ r2_hidden(X1,k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X16,X17)
        | ~ r2_hidden(X18,X16)
        | r2_hidden(X18,X17) )
      & ( r2_hidden(esk2_2(X19,X20),X19)
        | r1_tarski(X19,X20) )
      & ( ~ r2_hidden(esk2_2(X19,X20),X20)
        | r1_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | k1_zfmisc_1(esk5_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk7_0))
    | ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_20])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk2_2(X1,esk6_0),k4_xboole_0(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3)
    | r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r2_hidden(esk2_2(esk6_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,k4_xboole_0(esk5_0,X1)),X1)
    | r1_tarski(esk6_0,k4_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 = k4_xboole_0(esk5_0,esk7_0)
    | ~ r1_tarski(esk6_0,k4_xboole_0(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk6_0,k4_xboole_0(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 != k3_subset_1(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = k4_xboole_0(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( k3_subset_1(esk5_0,esk7_0) != k4_xboole_0(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_16]),c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
