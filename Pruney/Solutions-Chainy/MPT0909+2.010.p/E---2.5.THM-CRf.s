%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:09 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 228 expanded)
%              Number of clauses        :   40 ( 100 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 903 expanded)
%              Number of equality atoms :  103 ( 468 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X6 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X6 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_mcart_1])).

fof(c_0_13,negated_conjecture,(
    ! [X44,X45,X46] :
      ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
      & ( ~ m1_subset_1(X44,esk1_0)
        | ~ m1_subset_1(X45,esk2_0)
        | ~ m1_subset_1(X46,esk3_0)
        | esk5_0 != k3_mcart_1(X44,X45,X46)
        | esk4_0 = X44 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
    ! [X20,X21,X22] : k3_zfmisc_1(X20,X21,X22) = k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | X9 = X10
      | ~ v1_xboole_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X35,X36,X37,X38] :
      ( ( k5_mcart_1(X35,X36,X37,X38) = k1_mcart_1(k1_mcart_1(X38))
        | ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0 )
      & ( k6_mcart_1(X35,X36,X37,X38) = k2_mcart_1(k1_mcart_1(X38))
        | ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0 )
      & ( k7_mcart_1(X35,X36,X37,X38) = k2_mcart_1(X38)
        | ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
        | X35 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_24,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(k1_mcart_1(X27),X28)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) )
      & ( r2_hidden(k2_mcart_1(X27),X29)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | r2_hidden(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X32,X33,X34] :
      ( ( X32 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 = k1_xboole_0
        | k3_zfmisc_1(X32,X33,X34) != k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k3_zfmisc_1(X32,X33,X34) = k1_xboole_0 )
      & ( X33 != k1_xboole_0
        | k3_zfmisc_1(X32,X33,X34) = k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k3_zfmisc_1(X32,X33,X34) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

fof(c_0_31,plain,(
    ! [X17,X18,X19] : k3_mcart_1(X17,X18,X19) = k4_tarski(k4_tarski(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_32,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r2_hidden(X30,X31)
      | X30 = k4_tarski(k1_mcart_1(X30),k2_mcart_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_33,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_34,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_38,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | m1_subset_1(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk5_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | esk5_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 != k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) = k1_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_22]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(esk5_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(esk5_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_51,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = X1
    | esk5_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk5_0)),k2_mcart_1(k1_mcart_1(esk5_0))) = k1_mcart_1(esk5_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_39]),c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk5_0)) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(esk5_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(esk5_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(esk5_0),X1) != esk5_0
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_45])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_62]),c_0_35]),c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n023.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:39:51 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.14/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.14/0.37  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.14/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.37  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.14/0.37  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.14/0.37  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.14/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.14/0.37  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.14/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.14/0.37  fof(c_0_13, negated_conjecture, ![X44, X45, X46]:(m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&((~m1_subset_1(X44,esk1_0)|(~m1_subset_1(X45,esk2_0)|(~m1_subset_1(X46,esk3_0)|(esk5_0!=k3_mcart_1(X44,X45,X46)|esk4_0=X44))))&(((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.14/0.37  fof(c_0_14, plain, ![X20, X21, X22]:k3_zfmisc_1(X20,X21,X22)=k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.14/0.37  fof(c_0_15, plain, ![X9, X10]:(~v1_xboole_0(X9)|X9=X10|~v1_xboole_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.14/0.37  fof(c_0_16, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_18, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  cnf(c_0_19, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_20, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.37  cnf(c_0_21, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.37  fof(c_0_23, plain, ![X35, X36, X37, X38]:(((k5_mcart_1(X35,X36,X37,X38)=k1_mcart_1(k1_mcart_1(X38))|~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|(X35=k1_xboole_0|X36=k1_xboole_0|X37=k1_xboole_0))&(k6_mcart_1(X35,X36,X37,X38)=k2_mcart_1(k1_mcart_1(X38))|~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|(X35=k1_xboole_0|X36=k1_xboole_0|X37=k1_xboole_0)))&(k7_mcart_1(X35,X36,X37,X38)=k2_mcart_1(X38)|~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|(X35=k1_xboole_0|X36=k1_xboole_0|X37=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.14/0.37  fof(c_0_24, plain, ![X27, X28, X29]:((r2_hidden(k1_mcart_1(X27),X28)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))&(r2_hidden(k2_mcart_1(X27),X29)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.14/0.37  cnf(c_0_25, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.37  cnf(c_0_27, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_28, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|r2_hidden(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.37  fof(c_0_30, plain, ![X32, X33, X34]:((X32=k1_xboole_0|X33=k1_xboole_0|X34=k1_xboole_0|k3_zfmisc_1(X32,X33,X34)!=k1_xboole_0)&(((X32!=k1_xboole_0|k3_zfmisc_1(X32,X33,X34)=k1_xboole_0)&(X33!=k1_xboole_0|k3_zfmisc_1(X32,X33,X34)=k1_xboole_0))&(X34!=k1_xboole_0|k3_zfmisc_1(X32,X33,X34)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.14/0.37  fof(c_0_31, plain, ![X17, X18, X19]:k3_mcart_1(X17,X18,X19)=k4_tarski(k4_tarski(X17,X18),X19), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.14/0.37  fof(c_0_32, plain, ![X30, X31]:(~v1_relat_1(X31)|(~r2_hidden(X30,X31)|X30=k4_tarski(k1_mcart_1(X30),k2_mcart_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.14/0.37  fof(c_0_33, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.37  cnf(c_0_34, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_27, c_0_18])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  fof(c_0_38, plain, ![X11, X12]:(~r2_hidden(X11,X12)|m1_subset_1(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk5_0),k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.37  cnf(c_0_40, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (esk4_0=X1|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X3,esk3_0)|esk5_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_43, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_44, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.37  cnf(c_0_45, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.37  cnf(c_0_46, negated_conjecture, (esk4_0!=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_47, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)=k1_mcart_1(k1_mcart_1(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_22]), c_0_35]), c_0_36]), c_0_37])).
% 0.14/0.37  cnf(c_0_48, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.37  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(esk5_0)),esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_39])).
% 0.14/0.37  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|r2_hidden(k2_mcart_1(k1_mcart_1(esk5_0)),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.14/0.37  cnf(c_0_51, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_18])).
% 0.14/0.37  cnf(c_0_52, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|r2_hidden(k2_mcart_1(esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_29])).
% 0.14/0.37  cnf(c_0_53, negated_conjecture, (esk4_0=X1|esk5_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.37  cnf(c_0_54, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk5_0)),k2_mcart_1(k1_mcart_1(esk5_0)))=k1_mcart_1(esk5_0)|k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_39]), c_0_45])])).
% 0.14/0.37  cnf(c_0_55, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk5_0))!=esk4_0), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.37  cnf(c_0_56, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|m1_subset_1(k1_mcart_1(k1_mcart_1(esk5_0)),esk1_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.37  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|m1_subset_1(k2_mcart_1(k1_mcart_1(esk5_0)),esk2_0)), inference(spm,[status(thm)],[c_0_48, c_0_50])).
% 0.14/0.37  cnf(c_0_58, negated_conjecture, (r2_hidden(k2_mcart_1(esk5_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_35]), c_0_36]), c_0_37])).
% 0.14/0.37  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|k4_tarski(k1_mcart_1(esk5_0),X1)!=esk5_0|~m1_subset_1(X1,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57])).
% 0.14/0.37  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_45])])).
% 0.14/0.37  cnf(c_0_61, negated_conjecture, (m1_subset_1(k2_mcart_1(esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_58])).
% 0.14/0.37  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.14/0.37  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_62]), c_0_35]), c_0_36]), c_0_37]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 64
% 0.14/0.37  # Proof object clause steps            : 40
% 0.14/0.37  # Proof object formula steps           : 24
% 0.14/0.37  # Proof object conjectures             : 28
% 0.14/0.37  # Proof object clause conjectures      : 25
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 18
% 0.14/0.37  # Proof object initial formulas used   : 12
% 0.14/0.37  # Proof object generating inferences   : 17
% 0.14/0.37  # Proof object simplifying inferences  : 23
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 13
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 24
% 0.14/0.37  # Removed in clause preprocessing      : 2
% 0.14/0.37  # Initial clauses in saturation        : 22
% 0.14/0.37  # Processed clauses                    : 113
% 0.14/0.37  # ...of these trivial                  : 2
% 0.14/0.37  # ...subsumed                          : 8
% 0.14/0.37  # ...remaining for further processing  : 103
% 0.14/0.37  # Other redundant clauses eliminated   : 8
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 6
% 0.14/0.37  # Backward-rewritten                   : 22
% 0.14/0.37  # Generated clauses                    : 345
% 0.14/0.37  # ...of the previous two non-trivial   : 292
% 0.14/0.37  # Contextual simplify-reflections      : 4
% 0.14/0.37  # Paramodulations                      : 322
% 0.14/0.37  # Factorizations                       : 15
% 0.14/0.37  # Equation resolutions                 : 8
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 50
% 0.14/0.37  #    Positive orientable unit clauses  : 11
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 4
% 0.14/0.37  #    Non-unit-clauses                  : 35
% 0.14/0.37  # Current number of unprocessed clauses: 114
% 0.14/0.37  # ...number of literals in the above   : 465
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 52
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 167
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 97
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 17
% 0.14/0.37  # Unit Clause-clause subsumption calls : 9
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 8
% 0.14/0.37  # BW rewrite match successes           : 8
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 5577
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.035 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.040 s
% 0.14/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
