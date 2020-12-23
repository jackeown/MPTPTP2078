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
% DateTime   : Thu Dec  3 11:00:08 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :   94 (7373 expanded)
%              Number of clauses        :   63 (3707 expanded)
%              Number of leaves         :   15 (1799 expanded)
%              Depth                    :   19
%              Number of atoms          :  261 (19904 expanded)
%              Number of equality atoms :  135 (17857 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_15,plain,(
    ! [X45,X46,X47,X48] : k4_zfmisc_1(X45,X46,X47,X48) = k2_zfmisc_1(k3_zfmisc_1(X45,X46,X47),X48) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X42,X43,X44] : k3_zfmisc_1(X42,X43,X44) = k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X58,X59,X60,X61] :
      ( ( X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0
        | k4_zfmisc_1(X58,X59,X60,X61) != k1_xboole_0 )
      & ( X58 != k1_xboole_0
        | k4_zfmisc_1(X58,X59,X60,X61) = k1_xboole_0 )
      & ( X59 != k1_xboole_0
        | k4_zfmisc_1(X58,X59,X60,X61) = k1_xboole_0 )
      & ( X60 != k1_xboole_0
        | k4_zfmisc_1(X58,X59,X60,X61) = k1_xboole_0 )
      & ( X61 != k1_xboole_0
        | k4_zfmisc_1(X58,X59,X60,X61) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_18,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ r1_tarski(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_23,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_24,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( ~ r2_hidden(esk2_2(X13,X14),X13)
        | ~ r2_hidden(esk2_2(X13,X14),X14)
        | X13 = X14 )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r2_hidden(esk2_2(X13,X14),X14)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_31,negated_conjecture,(
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

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_30])).

fof(c_0_37,negated_conjecture,(
    ! [X67,X68,X69] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X67,esk4_0)
        | ~ m1_subset_1(X68,esk5_0)
        | ~ m1_subset_1(X69,esk6_0)
        | esk8_0 != k3_mcart_1(X67,X68,X69)
        | esk7_0 = X67 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])])).

cnf(c_0_38,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_30]),c_0_30]),c_0_30]),c_0_34])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_35]),c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),k1_xboole_0),k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | r2_hidden(esk2_2(k2_zfmisc_1(X3,X2),k1_xboole_0),k2_zfmisc_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

fof(c_0_44,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X32,X31)
        | r2_hidden(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ r2_hidden(X32,X31)
        | m1_subset_1(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ m1_subset_1(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_xboole_0(X31) )
      & ( ~ v1_xboole_0(X32)
        | m1_subset_1(X32,X31)
        | ~ v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),k1_xboole_0),k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_43]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_49,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,esk6_0),k1_xboole_0),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(k2_zfmisc_1(X1,esk5_0),k1_xboole_0),k2_zfmisc_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_55,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_2(k2_zfmisc_1(X1,esk6_0),k1_xboole_0),k2_zfmisc_1(X1,esk6_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_2(k2_zfmisc_1(esk4_0,esk5_0),k1_xboole_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_59,plain,(
    ! [X54,X55,X56,X57] :
      ( ( k5_mcart_1(X54,X55,X56,X57) = k1_mcart_1(k1_mcart_1(X57))
        | ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( k6_mcart_1(X54,X55,X56,X57) = k2_mcart_1(k1_mcart_1(X57))
        | ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 )
      & ( k7_mcart_1(X54,X55,X56,X57) = k2_mcart_1(X57)
        | ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
        | X54 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_60,plain,(
    ! [X49,X50,X51] :
      ( ( r2_hidden(k1_mcart_1(X49),X50)
        | ~ r2_hidden(X49,k2_zfmisc_1(X50,X51)) )
      & ( r2_hidden(k2_mcart_1(X49),X51)
        | ~ r2_hidden(X49,k2_zfmisc_1(X50,X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_2(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | ~ r2_hidden(X52,X53)
      | X52 = k4_tarski(k1_mcart_1(X52),k2_mcart_1(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_66,plain,(
    ! [X35,X36] : v1_relat_1(k2_zfmisc_1(X35,X36)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_67,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_19])).

cnf(c_0_70,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_19])).

fof(c_0_71,plain,(
    ! [X39,X40,X41] : k3_mcart_1(X39,X40,X41) = k4_tarski(k4_tarski(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_72,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_74,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | m1_subset_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_75,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk8_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_46]),c_0_48]),c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk8_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_51]),c_0_46]),c_0_48]),c_0_53])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 = X1
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_80,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_76]),c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( esk7_0 = X1
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) = k1_mcart_1(esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_76]),c_0_78]),c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),X1) != esk8_0
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88])]),c_0_41])).

cnf(c_0_91,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_68])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 6.02/6.18  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 6.02/6.18  # and selection function SelectNegativeLiterals.
% 6.02/6.18  #
% 6.02/6.18  # Preprocessing time       : 0.028 s
% 6.02/6.18  # Presaturation interreduction done
% 6.02/6.18  
% 6.02/6.18  # Proof found!
% 6.02/6.18  # SZS status Theorem
% 6.02/6.18  # SZS output start CNFRefutation
% 6.02/6.18  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 6.02/6.18  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.02/6.18  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 6.02/6.18  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.02/6.18  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.02/6.18  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 6.02/6.18  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 6.02/6.18  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.02/6.18  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.02/6.18  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.02/6.18  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 6.02/6.18  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 6.02/6.18  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.02/6.18  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.02/6.18  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 6.02/6.18  fof(c_0_15, plain, ![X45, X46, X47, X48]:k4_zfmisc_1(X45,X46,X47,X48)=k2_zfmisc_1(k3_zfmisc_1(X45,X46,X47),X48), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 6.02/6.18  fof(c_0_16, plain, ![X42, X43, X44]:k3_zfmisc_1(X42,X43,X44)=k2_zfmisc_1(k2_zfmisc_1(X42,X43),X44), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 6.02/6.18  fof(c_0_17, plain, ![X58, X59, X60, X61]:((X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0|k4_zfmisc_1(X58,X59,X60,X61)!=k1_xboole_0)&((((X58!=k1_xboole_0|k4_zfmisc_1(X58,X59,X60,X61)=k1_xboole_0)&(X59!=k1_xboole_0|k4_zfmisc_1(X58,X59,X60,X61)=k1_xboole_0))&(X60!=k1_xboole_0|k4_zfmisc_1(X58,X59,X60,X61)=k1_xboole_0))&(X61!=k1_xboole_0|k4_zfmisc_1(X58,X59,X60,X61)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 6.02/6.18  cnf(c_0_18, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.02/6.18  cnf(c_0_19, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.02/6.18  cnf(c_0_20, plain, (k4_zfmisc_1(X2,X3,X4,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.02/6.18  cnf(c_0_21, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 6.02/6.18  fof(c_0_22, plain, ![X37, X38]:(~r2_hidden(X37,X38)|~r1_tarski(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 6.02/6.18  fof(c_0_23, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 6.02/6.18  cnf(c_0_24, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.02/6.18  cnf(c_0_25, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 6.02/6.18  fof(c_0_26, plain, ![X13, X14]:((~r2_hidden(esk2_2(X13,X14),X13)|~r2_hidden(esk2_2(X13,X14),X14)|X13=X14)&(r2_hidden(esk2_2(X13,X14),X13)|r2_hidden(esk2_2(X13,X14),X14)|X13=X14)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 6.02/6.18  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.02/6.18  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.02/6.18  cnf(c_0_29, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_21])).
% 6.02/6.18  cnf(c_0_30, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 6.02/6.18  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 6.02/6.18  cnf(c_0_32, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.02/6.18  cnf(c_0_33, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.02/6.18  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 6.02/6.18  cnf(c_0_35, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 6.02/6.18  cnf(c_0_36, plain, (k2_zfmisc_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_30])).
% 6.02/6.18  fof(c_0_37, negated_conjecture, ![X67, X68, X69]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X67,esk4_0)|(~m1_subset_1(X68,esk5_0)|(~m1_subset_1(X69,esk6_0)|(esk8_0!=k3_mcart_1(X67,X68,X69)|esk7_0=X67))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])])).
% 6.02/6.18  cnf(c_0_38, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_21])).
% 6.02/6.18  cnf(c_0_39, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_33]), c_0_30]), c_0_30]), c_0_30]), c_0_34])).
% 6.02/6.18  cnf(c_0_40, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_35]), c_0_36])).
% 6.02/6.18  cnf(c_0_41, negated_conjecture, (esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.02/6.18  cnf(c_0_42, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),k1_xboole_0),k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_40])])).
% 6.02/6.18  cnf(c_0_43, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|r2_hidden(esk2_2(k2_zfmisc_1(X3,X2),k1_xboole_0),k2_zfmisc_1(X3,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 6.02/6.18  fof(c_0_44, plain, ![X31, X32]:(((~m1_subset_1(X32,X31)|r2_hidden(X32,X31)|v1_xboole_0(X31))&(~r2_hidden(X32,X31)|m1_subset_1(X32,X31)|v1_xboole_0(X31)))&((~m1_subset_1(X32,X31)|v1_xboole_0(X32)|~v1_xboole_0(X31))&(~v1_xboole_0(X32)|m1_subset_1(X32,X31)|~v1_xboole_0(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 6.02/6.18  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.02/6.18  cnf(c_0_46, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.02/6.18  cnf(c_0_47, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(esk2_2(k2_zfmisc_1(X1,X2),k1_xboole_0),k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_43]), c_0_43])).
% 6.02/6.18  cnf(c_0_48, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.02/6.18  fof(c_0_49, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 6.02/6.18  cnf(c_0_50, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 6.02/6.18  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_45, c_0_19])).
% 6.02/6.18  cnf(c_0_52, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_2(k2_zfmisc_1(X1,esk6_0),k1_xboole_0),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 6.02/6.18  cnf(c_0_53, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.02/6.18  cnf(c_0_54, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_2(k2_zfmisc_1(X1,esk5_0),k1_xboole_0),k2_zfmisc_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 6.02/6.18  cnf(c_0_55, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 6.02/6.18  cnf(c_0_56, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 6.02/6.18  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_2(k2_zfmisc_1(X1,esk6_0),k1_xboole_0),k2_zfmisc_1(X1,esk6_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_52])).
% 6.02/6.18  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_2(k2_zfmisc_1(esk4_0,esk5_0),k1_xboole_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 6.02/6.18  fof(c_0_59, plain, ![X54, X55, X56, X57]:(((k5_mcart_1(X54,X55,X56,X57)=k1_mcart_1(k1_mcart_1(X57))|~m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))|(X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0))&(k6_mcart_1(X54,X55,X56,X57)=k2_mcart_1(k1_mcart_1(X57))|~m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))|(X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0)))&(k7_mcart_1(X54,X55,X56,X57)=k2_mcart_1(X57)|~m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))|(X54=k1_xboole_0|X55=k1_xboole_0|X56=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 6.02/6.18  fof(c_0_60, plain, ![X49, X50, X51]:((r2_hidden(k1_mcart_1(X49),X50)|~r2_hidden(X49,k2_zfmisc_1(X50,X51)))&(r2_hidden(k2_mcart_1(X49),X51)|~r2_hidden(X49,k2_zfmisc_1(X50,X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 6.02/6.18  cnf(c_0_61, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 6.02/6.18  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_2(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),k1_xboole_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 6.02/6.18  cnf(c_0_63, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 6.02/6.18  cnf(c_0_64, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 6.02/6.18  fof(c_0_65, plain, ![X52, X53]:(~v1_relat_1(X53)|(~r2_hidden(X52,X53)|X52=k4_tarski(k1_mcart_1(X52),k2_mcart_1(X52)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 6.02/6.18  fof(c_0_66, plain, ![X35, X36]:v1_relat_1(k2_zfmisc_1(X35,X36)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 6.02/6.18  cnf(c_0_67, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.02/6.18  cnf(c_0_68, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 6.02/6.18  cnf(c_0_69, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_63, c_0_19])).
% 6.02/6.18  cnf(c_0_70, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_64, c_0_19])).
% 6.02/6.18  fof(c_0_71, plain, ![X39, X40, X41]:k3_mcart_1(X39,X40,X41)=k4_tarski(k4_tarski(X39,X40),X41), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 6.02/6.18  cnf(c_0_72, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 6.02/6.18  cnf(c_0_73, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 6.02/6.18  fof(c_0_74, plain, ![X33, X34]:(~r2_hidden(X33,X34)|m1_subset_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 6.02/6.18  cnf(c_0_75, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.02/6.18  cnf(c_0_76, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 6.02/6.18  cnf(c_0_77, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk8_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51]), c_0_46]), c_0_48]), c_0_53])).
% 6.02/6.18  cnf(c_0_78, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk8_0))=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_51]), c_0_46]), c_0_48]), c_0_53])).
% 6.02/6.18  cnf(c_0_79, negated_conjecture, (esk7_0=X1|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.02/6.18  cnf(c_0_80, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 6.02/6.18  cnf(c_0_81, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 6.02/6.18  cnf(c_0_82, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 6.02/6.18  cnf(c_0_83, negated_conjecture, (r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 6.02/6.18  cnf(c_0_84, negated_conjecture, (r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_76]), c_0_78])).
% 6.02/6.18  cnf(c_0_85, negated_conjecture, (esk7_0=X1|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 6.02/6.18  cnf(c_0_86, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))=k1_mcart_1(esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_76]), c_0_78]), c_0_77])).
% 6.02/6.18  cnf(c_0_87, negated_conjecture, (m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 6.02/6.18  cnf(c_0_88, negated_conjecture, (m1_subset_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(spm,[status(thm)],[c_0_82, c_0_84])).
% 6.02/6.18  cnf(c_0_89, negated_conjecture, (r2_hidden(k2_mcart_1(esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_68])).
% 6.02/6.18  cnf(c_0_90, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),X1)!=esk8_0|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88])]), c_0_41])).
% 6.02/6.18  cnf(c_0_91, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_81, c_0_68])).
% 6.02/6.18  cnf(c_0_92, negated_conjecture, (m1_subset_1(k2_mcart_1(esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_82, c_0_89])).
% 6.02/6.18  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])]), ['proof']).
% 6.02/6.18  # SZS output end CNFRefutation
% 6.02/6.18  # Proof object total steps             : 94
% 6.02/6.18  # Proof object clause steps            : 63
% 6.02/6.18  # Proof object formula steps           : 31
% 6.02/6.18  # Proof object conjectures             : 34
% 6.02/6.18  # Proof object clause conjectures      : 31
% 6.02/6.18  # Proof object formula conjectures     : 3
% 6.02/6.18  # Proof object initial clauses used    : 24
% 6.02/6.18  # Proof object initial formulas used   : 15
% 6.02/6.18  # Proof object generating inferences   : 29
% 6.02/6.18  # Proof object simplifying inferences  : 36
% 6.02/6.18  # Training examples: 0 positive, 0 negative
% 6.02/6.18  # Parsed axioms                        : 18
% 6.02/6.18  # Removed by relevancy pruning/SinE    : 0
% 6.02/6.18  # Initial clauses                      : 40
% 6.02/6.18  # Removed in clause preprocessing      : 5
% 6.02/6.18  # Initial clauses in saturation        : 35
% 6.02/6.18  # Processed clauses                    : 13381
% 6.02/6.18  # ...of these trivial                  : 1390
% 6.02/6.18  # ...subsumed                          : 9684
% 6.02/6.18  # ...remaining for further processing  : 2307
% 6.02/6.18  # Other redundant clauses eliminated   : 7498
% 6.02/6.18  # Clauses deleted for lack of memory   : 0
% 6.02/6.18  # Backward-subsumed                    : 236
% 6.02/6.18  # Backward-rewritten                   : 445
% 6.02/6.18  # Generated clauses                    : 1067035
% 6.02/6.18  # ...of the previous two non-trivial   : 904167
% 6.02/6.18  # Contextual simplify-reflections      : 89
% 6.02/6.18  # Paramodulations                      : 1058694
% 6.02/6.18  # Factorizations                       : 845
% 6.02/6.18  # Equation resolutions                 : 7498
% 6.02/6.18  # Propositional unsat checks           : 0
% 6.02/6.18  #    Propositional check models        : 0
% 6.02/6.18  #    Propositional check unsatisfiable : 0
% 6.02/6.18  #    Propositional clauses             : 0
% 6.02/6.18  #    Propositional clauses after purity: 0
% 6.02/6.18  #    Propositional unsat core size     : 0
% 6.02/6.18  #    Propositional preprocessing time  : 0.000
% 6.02/6.18  #    Propositional encoding time       : 0.000
% 6.02/6.18  #    Propositional solver time         : 0.000
% 6.02/6.18  #    Success case prop preproc time    : 0.000
% 6.02/6.18  #    Success case prop encoding time   : 0.000
% 6.02/6.18  #    Success case prop solver time     : 0.000
% 6.02/6.18  # Current number of processed clauses  : 1585
% 6.02/6.18  #    Positive orientable unit clauses  : 374
% 6.02/6.18  #    Positive unorientable unit clauses: 0
% 6.02/6.18  #    Negative unit clauses             : 5
% 6.02/6.18  #    Non-unit-clauses                  : 1206
% 6.02/6.18  # Current number of unprocessed clauses: 888244
% 6.02/6.18  # ...number of literals in the above   : 4864762
% 6.02/6.18  # Current number of archived formulas  : 0
% 6.02/6.18  # Current number of archived clauses   : 720
% 6.02/6.18  # Clause-clause subsumption calls (NU) : 918365
% 6.02/6.18  # Rec. Clause-clause subsumption calls : 437968
% 6.02/6.18  # Non-unit clause-clause subsumptions  : 9594
% 6.02/6.18  # Unit Clause-clause subsumption calls : 63718
% 6.02/6.18  # Rewrite failures with RHS unbound    : 0
% 6.02/6.18  # BW rewrite match attempts            : 811
% 6.02/6.18  # BW rewrite match successes           : 45
% 6.02/6.18  # Condensation attempts                : 0
% 6.02/6.18  # Condensation successes               : 0
% 6.02/6.18  # Termbank termtop insertions          : 21394126
% 6.02/6.22  
% 6.02/6.22  # -------------------------------------------------
% 6.02/6.22  # User time                : 5.562 s
% 6.02/6.22  # System time              : 0.306 s
% 6.02/6.22  # Total time               : 5.868 s
% 6.02/6.22  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
