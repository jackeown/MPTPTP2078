%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:24 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 156 expanded)
%              Number of clauses        :   44 (  80 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 582 expanded)
%              Number of equality atoms :   22 (  89 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t42_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(c_0_10,plain,(
    ! [X34] : ~ v1_xboole_0(k1_zfmisc_1(X34)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_11,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X33,X32)
        | r2_hidden(X33,X32)
        | v1_xboole_0(X32) )
      & ( ~ r2_hidden(X33,X32)
        | m1_subset_1(X33,X32)
        | v1_xboole_0(X32) )
      & ( ~ m1_subset_1(X33,X32)
        | v1_xboole_0(X33)
        | ~ v1_xboole_0(X32) )
      & ( ~ v1_xboole_0(X33)
        | m1_subset_1(X33,X32)
        | ~ v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t42_subset_1])).

fof(c_0_13,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | r1_tarski(X27,X25)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r1_tarski(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r2_hidden(esk3_2(X29,X30),X30)
        | ~ r1_tarski(esk3_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | r1_tarski(esk3_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k9_subset_1(esk4_0,esk5_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X23,X24)
      | r1_tarski(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

fof(c_0_31,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(k1_zfmisc_1(esk6_0),X1),k1_zfmisc_1(esk4_0))
    | r2_hidden(k1_zfmisc_1(esk6_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_zfmisc_1(esk6_0),k1_zfmisc_1(k1_zfmisc_1(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_38])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_40]),c_0_23])).

fof(c_0_45,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_46,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r1_tarski(X39,X40)
        | r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) )
      & ( ~ r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))
        | r1_tarski(X39,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_50,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X35))
      | k9_subset_1(X35,X36,X37) = k3_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k3_xboole_0(X1,esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_44])).

cnf(c_0_54,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_58,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k9_subset_1(esk4_0,esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( k9_subset_1(esk4_0,X1,esk6_0) = k3_xboole_0(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k3_xboole_0(X1,esk6_0)))
    | ~ r1_tarski(k3_xboole_0(X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k3_xboole_0(esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:17 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  # Version: 2.5pre002
% 0.18/0.34  # No SInE strategy applied
% 0.18/0.34  # Trying AutoSched0 for 299 seconds
% 7.07/7.26  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 7.07/7.26  # and selection function SelectCQIArNXTEqFirst.
% 7.07/7.26  #
% 7.07/7.26  # Preprocessing time       : 0.028 s
% 7.07/7.26  # Presaturation interreduction done
% 7.07/7.26  
% 7.07/7.26  # Proof found!
% 7.07/7.26  # SZS status Theorem
% 7.07/7.26  # SZS output start CNFRefutation
% 7.07/7.26  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 7.07/7.26  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 7.07/7.26  fof(t42_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 7.07/7.26  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.07/7.26  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.07/7.26  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.07/7.26  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.07/7.26  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.07/7.26  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 7.07/7.26  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.07/7.26  fof(c_0_10, plain, ![X34]:~v1_xboole_0(k1_zfmisc_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 7.07/7.26  fof(c_0_11, plain, ![X32, X33]:(((~m1_subset_1(X33,X32)|r2_hidden(X33,X32)|v1_xboole_0(X32))&(~r2_hidden(X33,X32)|m1_subset_1(X33,X32)|v1_xboole_0(X32)))&((~m1_subset_1(X33,X32)|v1_xboole_0(X33)|~v1_xboole_0(X32))&(~v1_xboole_0(X33)|m1_subset_1(X33,X32)|~v1_xboole_0(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 7.07/7.26  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t42_subset_1])).
% 7.07/7.26  fof(c_0_13, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|r1_tarski(X27,X25)|X26!=k1_zfmisc_1(X25))&(~r1_tarski(X28,X25)|r2_hidden(X28,X26)|X26!=k1_zfmisc_1(X25)))&((~r2_hidden(esk3_2(X29,X30),X30)|~r1_tarski(esk3_2(X29,X30),X29)|X30=k1_zfmisc_1(X29))&(r2_hidden(esk3_2(X29,X30),X30)|r1_tarski(esk3_2(X29,X30),X29)|X30=k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 7.07/7.26  cnf(c_0_14, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 7.07/7.26  cnf(c_0_15, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.07/7.26  fof(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))&~r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k9_subset_1(esk4_0,esk5_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 7.07/7.26  cnf(c_0_17, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.07/7.26  fof(c_0_18, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|~r1_tarski(X23,X24)|r1_tarski(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 7.07/7.26  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.07/7.26  cnf(c_0_20, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 7.07/7.26  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 7.07/7.26  fof(c_0_22, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 7.07/7.26  cnf(c_0_23, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_17])).
% 7.07/7.26  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.07/7.26  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_19])).
% 7.07/7.26  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 7.07/7.26  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.07/7.26  cnf(c_0_28, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 7.07/7.26  cnf(c_0_29, negated_conjecture, (r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 7.07/7.26  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 7.07/7.26  fof(c_0_31, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 7.07/7.26  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk4_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 7.07/7.26  cnf(c_0_33, plain, (r2_hidden(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)), inference(spm,[status(thm)],[c_0_25, c_0_30])).
% 7.07/7.26  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.07/7.26  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.07/7.26  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(k1_zfmisc_1(esk6_0),X1),k1_zfmisc_1(esk4_0))|r2_hidden(k1_zfmisc_1(esk6_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 7.07/7.26  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_34])).
% 7.07/7.26  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_zfmisc_1(esk6_0),k1_zfmisc_1(k1_zfmisc_1(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_23])).
% 7.07/7.26  cnf(c_0_39, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.07/7.26  cnf(c_0_40, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 7.07/7.26  cnf(c_0_41, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.07/7.26  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_38])).
% 7.07/7.26  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_39])).
% 7.07/7.26  cnf(c_0_44, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_40]), c_0_23])).
% 7.07/7.26  fof(c_0_45, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 7.07/7.26  fof(c_0_46, plain, ![X38, X39, X40]:((~r1_tarski(X39,X40)|r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))|~m1_subset_1(X40,k1_zfmisc_1(X38))|~m1_subset_1(X39,k1_zfmisc_1(X38)))&(~r1_tarski(k3_subset_1(X38,X40),k3_subset_1(X38,X39))|r1_tarski(X39,X40)|~m1_subset_1(X40,k1_zfmisc_1(X38))|~m1_subset_1(X39,k1_zfmisc_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 7.07/7.26  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk4_0))|~r2_hidden(X1,k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 7.07/7.26  cnf(c_0_48, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 7.07/7.26  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 7.07/7.26  fof(c_0_50, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X35))|k9_subset_1(X35,X36,X37)=k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 7.07/7.26  cnf(c_0_51, plain, (r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 7.07/7.26  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 7.07/7.26  cnf(c_0_53, negated_conjecture, (r2_hidden(k3_xboole_0(X1,esk6_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_44])).
% 7.07/7.26  cnf(c_0_54, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 7.07/7.26  cnf(c_0_55, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 7.07/7.26  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 7.07/7.26  cnf(c_0_57, negated_conjecture, (m1_subset_1(k3_xboole_0(X1,esk6_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_53])).
% 7.07/7.26  cnf(c_0_58, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_54])).
% 7.07/7.26  cnf(c_0_59, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k9_subset_1(esk4_0,esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 7.07/7.26  cnf(c_0_60, negated_conjecture, (k9_subset_1(esk4_0,X1,esk6_0)=k3_xboole_0(X1,esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_21])).
% 7.07/7.26  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k3_xboole_0(X1,esk6_0)))|~r1_tarski(k3_xboole_0(X1,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 7.07/7.26  cnf(c_0_62, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_25, c_0_58])).
% 7.07/7.26  cnf(c_0_63, negated_conjecture, (~r1_tarski(k3_subset_1(esk4_0,esk5_0),k3_subset_1(esk4_0,k3_xboole_0(esk5_0,esk6_0)))), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 7.07/7.26  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), ['proof']).
% 7.07/7.26  # SZS output end CNFRefutation
% 7.07/7.26  # Proof object total steps             : 65
% 7.07/7.26  # Proof object clause steps            : 44
% 7.07/7.26  # Proof object formula steps           : 21
% 7.07/7.26  # Proof object conjectures             : 20
% 7.07/7.26  # Proof object clause conjectures      : 17
% 7.07/7.26  # Proof object formula conjectures     : 3
% 7.07/7.26  # Proof object initial clauses used    : 16
% 7.07/7.26  # Proof object initial formulas used   : 10
% 7.07/7.26  # Proof object generating inferences   : 24
% 7.07/7.26  # Proof object simplifying inferences  : 7
% 7.07/7.26  # Training examples: 0 positive, 0 negative
% 7.07/7.26  # Parsed axioms                        : 10
% 7.07/7.26  # Removed by relevancy pruning/SinE    : 0
% 7.07/7.26  # Initial clauses                      : 26
% 7.07/7.26  # Removed in clause preprocessing      : 0
% 7.07/7.26  # Initial clauses in saturation        : 26
% 7.07/7.26  # Processed clauses                    : 16293
% 7.07/7.26  # ...of these trivial                  : 257
% 7.07/7.26  # ...subsumed                          : 9171
% 7.07/7.26  # ...remaining for further processing  : 6865
% 7.07/7.26  # Other redundant clauses eliminated   : 5
% 7.07/7.26  # Clauses deleted for lack of memory   : 0
% 7.07/7.26  # Backward-subsumed                    : 158
% 7.07/7.26  # Backward-rewritten                   : 236
% 7.07/7.26  # Generated clauses                    : 792709
% 7.07/7.26  # ...of the previous two non-trivial   : 756066
% 7.07/7.26  # Contextual simplify-reflections      : 109
% 7.07/7.26  # Paramodulations                      : 792504
% 7.07/7.26  # Factorizations                       : 200
% 7.07/7.26  # Equation resolutions                 : 5
% 7.07/7.26  # Propositional unsat checks           : 0
% 7.07/7.26  #    Propositional check models        : 0
% 7.07/7.26  #    Propositional check unsatisfiable : 0
% 7.07/7.26  #    Propositional clauses             : 0
% 7.07/7.26  #    Propositional clauses after purity: 0
% 7.07/7.26  #    Propositional unsat core size     : 0
% 7.07/7.26  #    Propositional preprocessing time  : 0.000
% 7.07/7.26  #    Propositional encoding time       : 0.000
% 7.07/7.26  #    Propositional solver time         : 0.000
% 7.07/7.26  #    Success case prop preproc time    : 0.000
% 7.07/7.26  #    Success case prop encoding time   : 0.000
% 7.07/7.26  #    Success case prop solver time     : 0.000
% 7.07/7.26  # Current number of processed clauses  : 6440
% 7.07/7.26  #    Positive orientable unit clauses  : 197
% 7.07/7.26  #    Positive unorientable unit clauses: 1
% 7.07/7.26  #    Negative unit clauses             : 13
% 7.07/7.26  #    Non-unit-clauses                  : 6229
% 7.07/7.26  # Current number of unprocessed clauses: 739496
% 7.07/7.26  # ...number of literals in the above   : 3857487
% 7.07/7.26  # Current number of archived formulas  : 0
% 7.07/7.26  # Current number of archived clauses   : 420
% 7.07/7.26  # Clause-clause subsumption calls (NU) : 7465599
% 7.07/7.26  # Rec. Clause-clause subsumption calls : 3234009
% 7.07/7.26  # Non-unit clause-clause subsumptions  : 9314
% 7.07/7.26  # Unit Clause-clause subsumption calls : 64397
% 7.07/7.26  # Rewrite failures with RHS unbound    : 0
% 7.07/7.26  # BW rewrite match attempts            : 668
% 7.07/7.26  # BW rewrite match successes           : 27
% 7.07/7.26  # Condensation attempts                : 0
% 7.07/7.26  # Condensation successes               : 0
% 7.07/7.26  # Termbank termtop insertions          : 15811376
% 7.07/7.29  
% 7.07/7.29  # -------------------------------------------------
% 7.07/7.29  # User time                : 6.688 s
% 7.07/7.29  # System time              : 0.239 s
% 7.07/7.29  # Total time               : 6.928 s
% 7.07/7.29  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
