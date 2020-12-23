%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0720+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 183 expanded)
%              Number of clauses        :   36 (  75 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 869 expanded)
%              Number of equality atoms :   26 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(t175_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & v5_funct_1(X2,X1) )
         => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( ( X16 != k1_funct_1(X14,X15)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ r2_hidden(X15,k1_relat_1(X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X16 = k1_funct_1(X14,X15)
        | ~ r2_hidden(X15,k1_relat_1(X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X16 != k1_funct_1(X14,X15)
        | X16 = k1_xboole_0
        | r2_hidden(X15,k1_relat_1(X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X16 != k1_xboole_0
        | X16 = k1_funct_1(X14,X15)
        | r2_hidden(X15,k1_relat_1(X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_10,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v5_funct_1(X5,X4)
        | ~ r2_hidden(X6,k1_relat_1(X5))
        | r2_hidden(k1_funct_1(X5,X6),k1_funct_1(X4,X6))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( r2_hidden(esk1_2(X4,X5),k1_relat_1(X5))
        | v5_funct_1(X5,X4)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( ~ r2_hidden(k1_funct_1(X5,esk1_2(X4,X5)),k1_funct_1(X4,esk1_2(X4,X5)))
        | v5_funct_1(X5,X4)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_funct_1(X2,X1) )
           => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_1])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))
    | ~ v5_funct_1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v5_funct_1(esk4_0,esk3_0)
    & ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_22,plain,(
    ! [X22] :
      ( ~ v1_xboole_0(X22)
      | X22 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X3,X2))
    | ~ v5_funct_1(X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v5_funct_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk4_0,X1),k1_funct_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_36,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(k1_funct_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k1_funct_1(X1,esk2_2(X2,k1_relat_1(X1))) = k1_xboole_0
    | r1_tarski(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_20])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_36])).

cnf(c_0_41,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | r2_hidden(k4_tarski(esk2_2(k1_relat_1(X1),X2),k1_funct_1(X1,esk2_2(k1_relat_1(X1),X2))),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_2(X1,k1_relat_1(esk3_0))) = k1_xboole_0
    | r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_27]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | r2_hidden(k1_funct_1(X1,esk2_2(k1_relat_1(X1),X2)),k1_funct_1(X3,esk2_2(k1_relat_1(X1),X2)))
    | ~ v5_funct_1(X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_46,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | X3 = k1_funct_1(X1,X2)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(k1_relat_1(esk4_0),k1_relat_1(esk3_0)),k1_xboole_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28]),c_0_30])]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | r2_hidden(k1_funct_1(esk4_0,esk2_2(k1_relat_1(esk4_0),X1)),k1_funct_1(esk3_0,esk2_2(k1_relat_1(esk4_0),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_2(k1_relat_1(esk4_0),k1_relat_1(esk3_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_28]),c_0_30])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_49]),c_0_27]),c_0_29])]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_40])]),
    [proof]).

%------------------------------------------------------------------------------
