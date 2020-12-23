%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:02 EST 2020

% Result     : Theorem 0.89s
% Output     : CNFRefutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 123 expanded)
%              Number of clauses        :   43 (  58 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 423 expanded)
%              Number of equality atoms :   23 (  55 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t158_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t153_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k9_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X1),X2),X1)
    | r1_tarski(k2_xboole_0(X1,X1),X2) ),
    inference(ef,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X4,X3),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_40,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_41,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | k9_relat_1(X35,k2_xboole_0(X33,X34)) = k2_xboole_0(k9_relat_1(X35,X33),k9_relat_1(X35,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_2(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X2),X1),X2)
    | r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | v1_relat_1(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_46,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_48,plain,
    ( k9_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_44])).

fof(c_0_51,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | ~ r1_tarski(X37,X38)
      | r1_tarski(k9_relat_1(X37,X36),k9_relat_1(X38,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

cnf(c_0_52,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k9_relat_1(X2,k2_xboole_0(X3,X4)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k9_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_49]),c_0_50])])).

cnf(c_0_56,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k9_relat_1(X2,esk4_0))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k9_relat_1(X2,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k9_relat_1(X4,X3))
    | ~ r1_tarski(X4,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_63,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_60]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:38:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.89/1.08  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.89/1.08  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.89/1.08  #
% 0.89/1.08  # Preprocessing time       : 0.028 s
% 0.89/1.08  # Presaturation interreduction done
% 0.89/1.08  
% 0.89/1.08  # Proof found!
% 0.89/1.08  # SZS status Theorem
% 0.89/1.08  # SZS output start CNFRefutation
% 0.89/1.08  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.89/1.08  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.89/1.08  fof(t158_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.89/1.08  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.89/1.08  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.89/1.08  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.89/1.08  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.89/1.08  fof(t153_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k9_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 0.89/1.08  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.89/1.08  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.89/1.08  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 0.89/1.08  fof(c_0_11, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.89/1.08  cnf(c_0_12, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.89/1.08  fof(c_0_13, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.89/1.08  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t158_relat_1])).
% 0.89/1.08  cnf(c_0_15, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.89/1.08  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.89/1.08  cnf(c_0_17, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.89/1.08  fof(c_0_18, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|~r1_tarski(X25,X26)|r1_tarski(X24,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.89/1.08  fof(c_0_19, negated_conjecture, (v1_relat_1(esk5_0)&(v1_relat_1(esk6_0)&((r1_tarski(esk5_0,esk6_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.89/1.08  cnf(c_0_20, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)|r1_tarski(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.89/1.08  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.89/1.08  cnf(c_0_22, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_17])).
% 0.89/1.08  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.89/1.08  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.89/1.08  fof(c_0_25, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.89/1.08  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.89/1.08  cnf(c_0_27, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X1),X2),X1)|r1_tarski(k2_xboole_0(X1,X1),X2)), inference(ef,[status(thm)],[c_0_20])).
% 0.89/1.08  fof(c_0_28, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.89/1.08  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(k2_xboole_0(X4,X3),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.89/1.08  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.89/1.08  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.89/1.08  cnf(c_0_32, plain, (r1_tarski(k2_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.89/1.08  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.89/1.08  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(X3,X2),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.89/1.08  cnf(c_0_35, plain, (k2_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.89/1.08  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.89/1.08  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,X2)|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.89/1.08  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.89/1.08  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.89/1.08  fof(c_0_40, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.89/1.08  fof(c_0_41, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|k9_relat_1(X35,k2_xboole_0(X33,X34))=k2_xboole_0(k9_relat_1(X35,X33),k9_relat_1(X35,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).
% 0.89/1.08  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(esk1_2(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.89/1.08  cnf(c_0_43, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X2),X1),X2)|r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.89/1.08  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.89/1.08  fof(c_0_45, plain, ![X31, X32]:(~v1_relat_1(X31)|(~m1_subset_1(X32,k1_zfmisc_1(X31))|v1_relat_1(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.89/1.08  fof(c_0_46, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.89/1.08  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.89/1.08  cnf(c_0_48, plain, (k9_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.89/1.08  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.89/1.08  cnf(c_0_50, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_33, c_0_44])).
% 0.89/1.08  fof(c_0_51, plain, ![X36, X37, X38]:(~v1_relat_1(X37)|(~v1_relat_1(X38)|(~r1_tarski(X37,X38)|r1_tarski(k9_relat_1(X37,X36),k9_relat_1(X38,X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.89/1.08  cnf(c_0_52, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.89/1.08  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.89/1.08  cnf(c_0_54, plain, (r1_tarski(X1,k9_relat_1(X2,k2_xboole_0(X3,X4)))|~v1_relat_1(X2)|~r1_tarski(X1,k9_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.89/1.08  cnf(c_0_55, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_49]), c_0_50])])).
% 0.89/1.08  cnf(c_0_56, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.89/1.08  cnf(c_0_57, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.89/1.08  cnf(c_0_58, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.89/1.08  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k9_relat_1(X2,esk4_0))|~v1_relat_1(X2)|~r1_tarski(X1,k9_relat_1(X2,esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.89/1.08  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.89/1.08  cnf(c_0_61, plain, (r1_tarski(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r1_tarski(X1,k9_relat_1(X4,X3))|~r1_tarski(X4,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_56]), c_0_57])).
% 0.89/1.08  cnf(c_0_62, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.89/1.08  cnf(c_0_63, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X3,X2))|~v1_relat_1(X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 0.89/1.08  cnf(c_0_64, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.89/1.08  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_60]), c_0_64])]), ['proof']).
% 0.89/1.08  # SZS output end CNFRefutation
% 0.89/1.08  # Proof object total steps             : 66
% 0.89/1.08  # Proof object clause steps            : 43
% 0.89/1.08  # Proof object formula steps           : 23
% 0.89/1.08  # Proof object conjectures             : 17
% 0.89/1.08  # Proof object clause conjectures      : 14
% 0.89/1.08  # Proof object formula conjectures     : 3
% 0.89/1.08  # Proof object initial clauses used    : 18
% 0.89/1.08  # Proof object initial formulas used   : 11
% 0.89/1.08  # Proof object generating inferences   : 22
% 0.89/1.08  # Proof object simplifying inferences  : 14
% 0.89/1.08  # Training examples: 0 positive, 0 negative
% 0.89/1.08  # Parsed axioms                        : 11
% 0.89/1.08  # Removed by relevancy pruning/SinE    : 0
% 0.89/1.08  # Initial clauses                      : 25
% 0.89/1.08  # Removed in clause preprocessing      : 0
% 0.89/1.08  # Initial clauses in saturation        : 25
% 0.89/1.08  # Processed clauses                    : 8006
% 0.89/1.08  # ...of these trivial                  : 151
% 0.89/1.08  # ...subsumed                          : 5737
% 0.89/1.08  # ...remaining for further processing  : 2118
% 0.89/1.08  # Other redundant clauses eliminated   : 5
% 0.89/1.08  # Clauses deleted for lack of memory   : 0
% 0.89/1.08  # Backward-subsumed                    : 251
% 0.89/1.08  # Backward-rewritten                   : 5
% 0.89/1.08  # Generated clauses                    : 55339
% 0.89/1.08  # ...of the previous two non-trivial   : 52834
% 0.89/1.08  # Contextual simplify-reflections      : 320
% 0.89/1.08  # Paramodulations                      : 54866
% 0.89/1.08  # Factorizations                       : 468
% 0.89/1.08  # Equation resolutions                 : 5
% 0.89/1.08  # Propositional unsat checks           : 0
% 0.89/1.08  #    Propositional check models        : 0
% 0.89/1.08  #    Propositional check unsatisfiable : 0
% 0.89/1.08  #    Propositional clauses             : 0
% 0.89/1.08  #    Propositional clauses after purity: 0
% 0.89/1.08  #    Propositional unsat core size     : 0
% 0.89/1.08  #    Propositional preprocessing time  : 0.000
% 0.89/1.08  #    Propositional encoding time       : 0.000
% 0.89/1.08  #    Propositional solver time         : 0.000
% 0.89/1.08  #    Success case prop preproc time    : 0.000
% 0.89/1.08  #    Success case prop encoding time   : 0.000
% 0.89/1.08  #    Success case prop solver time     : 0.000
% 0.89/1.08  # Current number of processed clauses  : 1833
% 0.89/1.08  #    Positive orientable unit clauses  : 106
% 0.89/1.08  #    Positive unorientable unit clauses: 1
% 0.89/1.08  #    Negative unit clauses             : 3
% 0.89/1.08  #    Non-unit-clauses                  : 1723
% 0.89/1.08  # Current number of unprocessed clauses: 44645
% 0.89/1.08  # ...number of literals in the above   : 172779
% 0.89/1.08  # Current number of archived formulas  : 0
% 0.89/1.08  # Current number of archived clauses   : 280
% 0.89/1.08  # Clause-clause subsumption calls (NU) : 587894
% 0.89/1.08  # Rec. Clause-clause subsumption calls : 246210
% 0.89/1.08  # Non-unit clause-clause subsumptions  : 5914
% 0.89/1.08  # Unit Clause-clause subsumption calls : 2653
% 0.89/1.08  # Rewrite failures with RHS unbound    : 0
% 0.89/1.08  # BW rewrite match attempts            : 1464
% 0.89/1.08  # BW rewrite match successes           : 8
% 0.89/1.08  # Condensation attempts                : 0
% 0.89/1.08  # Condensation successes               : 0
% 0.89/1.08  # Termbank termtop insertions          : 995198
% 0.92/1.08  
% 0.92/1.08  # -------------------------------------------------
% 0.92/1.08  # User time                : 0.720 s
% 0.92/1.08  # System time              : 0.021 s
% 0.92/1.08  # Total time               : 0.742 s
% 0.92/1.08  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
