%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 354 expanded)
%              Number of clauses        :   55 ( 149 expanded)
%              Number of leaves         :   13 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  271 (1673 expanded)
%              Number of equality atoms :  143 ( 850 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X8 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t24_mcart_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X8 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_mcart_1])).

fof(c_0_14,plain,(
    ! [X56,X57,X58] :
      ( ( r2_hidden(k1_mcart_1(X56),X57)
        | ~ r2_hidden(X56,k2_zfmisc_1(X57,X58)) )
      & ( r2_hidden(k2_mcart_1(X56),X58)
        | ~ r2_hidden(X56,k2_zfmisc_1(X57,X58)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_15,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X35,X34)
        | r2_hidden(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ r2_hidden(X35,X34)
        | m1_subset_1(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ m1_subset_1(X35,X34)
        | v1_xboole_0(X35)
        | ~ v1_xboole_0(X34) )
      & ( ~ v1_xboole_0(X35)
        | m1_subset_1(X35,X34)
        | ~ v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X74,X75,X76] :
      ( m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0))
      & ( ~ m1_subset_1(X74,esk8_0)
        | ~ m1_subset_1(X75,esk9_0)
        | ~ m1_subset_1(X76,esk10_0)
        | esk12_0 != k3_mcart_1(X74,X75,X76)
        | esk11_0 = X76 )
      & esk8_0 != k1_xboole_0
      & esk9_0 != k1_xboole_0
      & esk10_0 != k1_xboole_0
      & esk11_0 != k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X41,X42,X43] : k3_zfmisc_1(X41,X42,X43) = k2_zfmisc_1(k2_zfmisc_1(X41,X42),X43) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X62,X63,X64] :
      ( ( X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0
        | k3_zfmisc_1(X62,X63,X64) != k1_xboole_0 )
      & ( X62 != k1_xboole_0
        | k3_zfmisc_1(X62,X63,X64) = k1_xboole_0 )
      & ( X63 != k1_xboole_0
        | k3_zfmisc_1(X62,X63,X64) = k1_xboole_0 )
      & ( X64 != k1_xboole_0
        | k3_zfmisc_1(X62,X63,X64) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_38,plain,(
    ! [X38,X39,X40] : k3_mcart_1(X38,X39,X40) = k4_tarski(k4_tarski(X38,X39),X40) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_39,plain,(
    ! [X59,X60,X61] :
      ( X59 = k1_xboole_0
      | X60 = k1_xboole_0
      | ~ m1_subset_1(X61,k2_zfmisc_1(X59,X60))
      | X61 = k4_tarski(k1_mcart_1(X61),k2_mcart_1(X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_mcart_1])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( esk11_0 = X3
    | ~ m1_subset_1(X1,esk8_0)
    | ~ m1_subset_1(X2,esk9_0)
    | ~ m1_subset_1(X3,esk10_0)
    | esk12_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))
    | ~ m1_subset_1(X3,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk12_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk12_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | v1_xboole_0(k2_zfmisc_1(X3,X2))
    | ~ m1_subset_1(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21])).

fof(c_0_50,plain,(
    ! [X32,X33] :
      ( ( k2_zfmisc_1(X32,X33) != k1_xboole_0
        | X32 = k1_xboole_0
        | X33 = k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k2_zfmisc_1(X32,X33) = k1_xboole_0 )
      & ( X33 != k1_xboole_0
        | k2_zfmisc_1(X32,X33) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_51,negated_conjecture,
    ( esk11_0 = X3
    | esk12_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk10_0)
    | ~ m1_subset_1(X2,esk9_0)
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk12_0)),k2_mcart_1(k1_mcart_1(esk12_0))) = k1_mcart_1(esk12_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_36]),c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk12_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk12_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk12_0),esk10_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk12_0),k2_mcart_1(esk12_0)) = esk12_0
    | k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_35])).

cnf(c_0_58,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( esk11_0 = X1
    | k4_tarski(k1_mcart_1(esk12_0),X1) != esk12_0
    | ~ m1_subset_1(X1,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk12_0),esk10_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk12_0),k2_mcart_1(esk12_0)) = esk12_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36]),c_0_37])).

fof(c_0_62,plain,(
    ! [X65,X66,X67,X68] :
      ( ( k5_mcart_1(X65,X66,X67,X68) = k1_mcart_1(k1_mcart_1(X68))
        | ~ m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0 )
      & ( k6_mcart_1(X65,X66,X67,X68) = k2_mcart_1(k1_mcart_1(X68))
        | ~ m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0 )
      & ( k7_mcart_1(X65,X66,X67,X68) = k2_mcart_1(X68)
        | ~ m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | X67 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_63,plain,(
    ! [X15,X16,X17,X18,X21,X22,X23,X24,X25,X26,X28,X29] :
      ( ( r2_hidden(esk3_4(X15,X16,X17,X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( r2_hidden(esk4_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( X18 = k4_tarski(esk3_4(X15,X16,X17,X18),esk4_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(X22,X15)
        | ~ r2_hidden(X23,X16)
        | X21 != k4_tarski(X22,X23)
        | r2_hidden(X21,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X29,X25)
        | esk5_3(X24,X25,X26) != k4_tarski(X28,X29)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk6_3(X24,X25,X26),X24)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk7_3(X24,X25,X26),X25)
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( esk5_3(X24,X25,X26) = k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26))
        | r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_23])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( esk11_0 != k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( esk11_0 = k2_mcart_1(esk12_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_68,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))
    | k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) != k2_mcart_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_23])).

cnf(c_0_73,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_69])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_28])]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_77,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_41])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_78]),c_0_35]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.20/0.40  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.20/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.40  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.40  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.20/0.40  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.40  fof(t24_mcart_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 0.20/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.40  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.20/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.20/0.40  fof(c_0_14, plain, ![X56, X57, X58]:((r2_hidden(k1_mcart_1(X56),X57)|~r2_hidden(X56,k2_zfmisc_1(X57,X58)))&(r2_hidden(k2_mcart_1(X56),X58)|~r2_hidden(X56,k2_zfmisc_1(X57,X58)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.20/0.40  fof(c_0_15, plain, ![X34, X35]:(((~m1_subset_1(X35,X34)|r2_hidden(X35,X34)|v1_xboole_0(X34))&(~r2_hidden(X35,X34)|m1_subset_1(X35,X34)|v1_xboole_0(X34)))&((~m1_subset_1(X35,X34)|v1_xboole_0(X35)|~v1_xboole_0(X34))&(~v1_xboole_0(X35)|m1_subset_1(X35,X34)|~v1_xboole_0(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.40  fof(c_0_16, negated_conjecture, ![X74, X75, X76]:(m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0))&((~m1_subset_1(X74,esk8_0)|(~m1_subset_1(X75,esk9_0)|(~m1_subset_1(X76,esk10_0)|(esk12_0!=k3_mcart_1(X74,X75,X76)|esk11_0=X76))))&(((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&esk10_0!=k1_xboole_0)&esk11_0!=k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.20/0.40  fof(c_0_17, plain, ![X41, X42, X43]:k3_zfmisc_1(X41,X42,X43)=k2_zfmisc_1(k2_zfmisc_1(X41,X42),X43), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.40  fof(c_0_18, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  fof(c_0_19, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.40  cnf(c_0_20, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_21, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_23, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_24, plain, ![X62, X63, X64]:((X62=k1_xboole_0|X63=k1_xboole_0|X64=k1_xboole_0|k3_zfmisc_1(X62,X63,X64)!=k1_xboole_0)&(((X62!=k1_xboole_0|k3_zfmisc_1(X62,X63,X64)=k1_xboole_0)&(X63!=k1_xboole_0|k3_zfmisc_1(X62,X63,X64)=k1_xboole_0))&(X64!=k1_xboole_0|k3_zfmisc_1(X62,X63,X64)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.20/0.40  cnf(c_0_25, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_27, plain, (r2_hidden(k1_mcart_1(X1),X2)|v1_xboole_0(k2_zfmisc_1(X2,X3))|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.40  cnf(c_0_29, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_30, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.40  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_33, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_23])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  fof(c_0_38, plain, ![X38, X39, X40]:k3_mcart_1(X38,X39,X40)=k4_tarski(k4_tarski(X38,X39),X40), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.40  fof(c_0_39, plain, ![X59, X60, X61]:(X59=k1_xboole_0|X60=k1_xboole_0|(~m1_subset_1(X61,k2_zfmisc_1(X59,X60))|X61=k4_tarski(k1_mcart_1(X61),k2_mcart_1(X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_mcart_1])])])).
% 0.20/0.40  cnf(c_0_40, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_32, c_0_25])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.20/0.40  cnf(c_0_42, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (esk11_0=X3|~m1_subset_1(X1,esk8_0)|~m1_subset_1(X2,esk9_0)|~m1_subset_1(X3,esk10_0)|esk12_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_44, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))|~m1_subset_1(X3,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (m1_subset_1(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk12_0)),esk9_0)), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk12_0)),esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_41])).
% 0.20/0.40  cnf(c_0_49, plain, (r2_hidden(k2_mcart_1(X1),X2)|v1_xboole_0(k2_zfmisc_1(X3,X2))|~m1_subset_1(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_42, c_0_21])).
% 0.20/0.40  fof(c_0_50, plain, ![X32, X33]:((k2_zfmisc_1(X32,X33)!=k1_xboole_0|(X32=k1_xboole_0|X33=k1_xboole_0))&((X32!=k1_xboole_0|k2_zfmisc_1(X32,X33)=k1_xboole_0)&(X33!=k1_xboole_0|k2_zfmisc_1(X32,X33)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (esk11_0=X3|esk12_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk10_0)|~m1_subset_1(X2,esk9_0)|~m1_subset_1(X1,esk8_0)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk12_0)),k2_mcart_1(k1_mcart_1(esk12_0)))=k1_mcart_1(esk12_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_36]), c_0_37])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk12_0)),esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk12_0)),esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_48])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (r2_hidden(k2_mcart_1(esk12_0),esk10_0)|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_49, c_0_28])).
% 0.20/0.40  cnf(c_0_56, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (k4_tarski(k1_mcart_1(esk12_0),k2_mcart_1(esk12_0))=esk12_0|k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_28]), c_0_35])).
% 0.20/0.40  cnf(c_0_58, plain, (k3_zfmisc_1(X2,X1,X3)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (esk11_0=X1|k4_tarski(k1_mcart_1(esk12_0),X1)!=esk12_0|~m1_subset_1(X1,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (m1_subset_1(k2_mcart_1(esk12_0),esk10_0)|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_40, c_0_55])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k4_tarski(k1_mcart_1(esk12_0),k2_mcart_1(esk12_0))=esk12_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_36]), c_0_37])).
% 0.20/0.40  fof(c_0_62, plain, ![X65, X66, X67, X68]:(((k5_mcart_1(X65,X66,X67,X68)=k1_mcart_1(k1_mcart_1(X68))|~m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))|(X65=k1_xboole_0|X66=k1_xboole_0|X67=k1_xboole_0))&(k6_mcart_1(X65,X66,X67,X68)=k2_mcart_1(k1_mcart_1(X68))|~m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))|(X65=k1_xboole_0|X66=k1_xboole_0|X67=k1_xboole_0)))&(k7_mcart_1(X65,X66,X67,X68)=k2_mcart_1(X68)|~m1_subset_1(X68,k3_zfmisc_1(X65,X66,X67))|(X65=k1_xboole_0|X66=k1_xboole_0|X67=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.20/0.40  fof(c_0_63, plain, ![X15, X16, X17, X18, X21, X22, X23, X24, X25, X26, X28, X29]:(((((r2_hidden(esk3_4(X15,X16,X17,X18),X15)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16))&(r2_hidden(esk4_4(X15,X16,X17,X18),X16)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(X18=k4_tarski(esk3_4(X15,X16,X17,X18),esk4_4(X15,X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(~r2_hidden(X22,X15)|~r2_hidden(X23,X16)|X21!=k4_tarski(X22,X23)|r2_hidden(X21,X17)|X17!=k2_zfmisc_1(X15,X16)))&((~r2_hidden(esk5_3(X24,X25,X26),X26)|(~r2_hidden(X28,X24)|~r2_hidden(X29,X25)|esk5_3(X24,X25,X26)!=k4_tarski(X28,X29))|X26=k2_zfmisc_1(X24,X25))&(((r2_hidden(esk6_3(X24,X25,X26),X24)|r2_hidden(esk5_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))&(r2_hidden(esk7_3(X24,X25,X26),X25)|r2_hidden(esk5_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25)))&(esk5_3(X24,X25,X26)=k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26))|r2_hidden(esk5_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.40  cnf(c_0_64, plain, (k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_23])).
% 0.20/0.40  cnf(c_0_65, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (esk11_0!=k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (esk11_0=k2_mcart_1(esk12_0)|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.20/0.40  cnf(c_0_68, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.40  cnf(c_0_69, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.40  cnf(c_0_70, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))|k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)!=k2_mcart_1(esk12_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.40  cnf(c_0_72, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_68, c_0_23])).
% 0.20/0.40  cnf(c_0_73, plain, (X1!=k2_zfmisc_1(X2,X3)|~r2_hidden(X4,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_25, c_0_69])).
% 0.20/0.40  cnf(c_0_74, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_70])).
% 0.20/0.40  cnf(c_0_75, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_28])]), c_0_35]), c_0_36]), c_0_37])).
% 0.20/0.40  cnf(c_0_77, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_76])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_41])).
% 0.20/0.40  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_78]), c_0_35]), c_0_79]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 81
% 0.20/0.40  # Proof object clause steps            : 55
% 0.20/0.40  # Proof object formula steps           : 26
% 0.20/0.40  # Proof object conjectures             : 31
% 0.20/0.40  # Proof object clause conjectures      : 28
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 22
% 0.20/0.40  # Proof object initial formulas used   : 13
% 0.20/0.40  # Proof object generating inferences   : 27
% 0.20/0.40  # Proof object simplifying inferences  : 28
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 17
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 41
% 0.20/0.40  # Removed in clause preprocessing      : 2
% 0.20/0.40  # Initial clauses in saturation        : 39
% 0.20/0.40  # Processed clauses                    : 632
% 0.20/0.40  # ...of these trivial                  : 8
% 0.20/0.40  # ...subsumed                          : 443
% 0.20/0.40  # ...remaining for further processing  : 181
% 0.20/0.40  # Other redundant clauses eliminated   : 1
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 4
% 0.20/0.40  # Backward-rewritten                   : 15
% 0.20/0.40  # Generated clauses                    : 1482
% 0.20/0.40  # ...of the previous two non-trivial   : 982
% 0.20/0.40  # Contextual simplify-reflections      : 5
% 0.20/0.40  # Paramodulations                      : 1470
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 12
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 125
% 0.20/0.40  #    Positive orientable unit clauses  : 12
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 9
% 0.20/0.40  #    Non-unit-clauses                  : 104
% 0.20/0.40  # Current number of unprocessed clauses: 361
% 0.20/0.40  # ...number of literals in the above   : 1440
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 58
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1173
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 815
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 251
% 0.20/0.40  # Unit Clause-clause subsumption calls : 24
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 6
% 0.20/0.40  # BW rewrite match successes           : 6
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 16672
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.054 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
