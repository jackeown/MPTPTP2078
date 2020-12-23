%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 513 expanded)
%              Number of clauses        :   29 ( 156 expanded)
%              Number of leaves         :    4 ( 126 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 (4862 expanded)
%              Number of equality atoms :  139 (2932 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
     => ( ! [X7] :
            ( m1_subset_1(X7,X1)
           => ! [X8] :
                ( m1_subset_1(X8,X2)
               => ! [X9] :
                    ( m1_subset_1(X9,X3)
                   => ! [X10] :
                        ( m1_subset_1(X10,X4)
                       => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                         => X5 = X7 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k8_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

fof(l68_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ? [X5] :
            ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ! [X8] :
                        ( m1_subset_1(X8,X3)
                       => ! [X9] :
                            ( m1_subset_1(X9,X4)
                           => X5 != k4_mcart_1(X6,X7,X8,X9) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

fof(d8_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ( X6 = k8_mcart_1(X1,X2,X3,X4,X5)
                  <=> ! [X7,X8,X9,X10] :
                        ( X5 = k4_mcart_1(X7,X8,X9,X10)
                       => X6 = X7 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_mcart_1)).

fof(t33_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
       => ( ! [X7] :
              ( m1_subset_1(X7,X1)
             => ! [X8] :
                  ( m1_subset_1(X8,X2)
                 => ! [X9] :
                      ( m1_subset_1(X9,X3)
                     => ! [X10] :
                          ( m1_subset_1(X10,X4)
                         => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                           => X5 = X7 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k8_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t79_mcart_1])).

fof(c_0_5,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( m1_subset_1(esk5_5(X25,X26,X27,X28,X29),X25)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( m1_subset_1(esk6_5(X25,X26,X27,X28,X29),X26)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( m1_subset_1(esk7_5(X25,X26,X27,X28,X29),X27)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( m1_subset_1(esk8_5(X25,X26,X27,X28,X29),X28)
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 )
      & ( X29 = k4_mcart_1(esk5_5(X25,X26,X27,X28,X29),esk6_5(X25,X26,X27,X28,X29),esk7_5(X25,X26,X27,X28,X29),esk8_5(X25,X26,X27,X28,X29))
        | ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X48,X49,X50,X51] :
      ( m1_subset_1(esk14_0,k4_zfmisc_1(esk9_0,esk10_0,esk11_0,esk12_0))
      & ( ~ m1_subset_1(X48,esk9_0)
        | ~ m1_subset_1(X49,esk10_0)
        | ~ m1_subset_1(X50,esk11_0)
        | ~ m1_subset_1(X51,esk12_0)
        | esk14_0 != k4_mcart_1(X48,X49,X50,X51)
        | esk13_0 = X48 )
      & esk9_0 != k1_xboole_0
      & esk10_0 != k1_xboole_0
      & esk11_0 != k1_xboole_0
      & esk12_0 != k1_xboole_0
      & esk13_0 != k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( X1 = k4_mcart_1(esk5_5(X2,X3,X4,X5,X1),esk6_5(X2,X3,X4,X5,X1),esk7_5(X2,X3,X4,X5,X1),esk8_5(X2,X3,X4,X5,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk14_0,k4_zfmisc_1(esk9_0,esk10_0,esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( esk12_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk8_5(X1,X2,X3,X4,X5),X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk7_5(X1,X2,X3,X4,X5),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk6_5(X1,X2,X3,X4,X5),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( esk13_0 = X1
    | ~ m1_subset_1(X1,esk9_0)
    | ~ m1_subset_1(X2,esk10_0)
    | ~ m1_subset_1(X3,esk11_0)
    | ~ m1_subset_1(X4,esk12_0)
    | esk14_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( k4_mcart_1(esk5_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk6_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk7_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk8_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)) = esk14_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk12_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk11_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

fof(c_0_23,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( X16 != k8_mcart_1(X11,X12,X13,X14,X15)
        | X15 != k4_mcart_1(X17,X18,X19,X20)
        | X16 = X17
        | ~ m1_subset_1(X16,X11)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X15 = k4_mcart_1(esk1_6(X11,X12,X13,X14,X15,X16),esk2_6(X11,X12,X13,X14,X15,X16),esk3_6(X11,X12,X13,X14,X15,X16),esk4_6(X11,X12,X13,X14,X15,X16))
        | X16 = k8_mcart_1(X11,X12,X13,X14,X15)
        | ~ m1_subset_1(X16,X11)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X16 != esk1_6(X11,X12,X13,X14,X15,X16)
        | X16 = k8_mcart_1(X11,X12,X13,X14,X15)
        | ~ m1_subset_1(X16,X11)
        | ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_mcart_1])])])])])])).

fof(c_0_24,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40,X41] :
      ( ( X34 = X38
        | k4_mcart_1(X34,X35,X36,X37) != k4_mcart_1(X38,X39,X40,X41) )
      & ( X35 = X39
        | k4_mcart_1(X34,X35,X36,X37) != k4_mcart_1(X38,X39,X40,X41) )
      & ( X36 = X40
        | k4_mcart_1(X34,X35,X36,X37) != k4_mcart_1(X38,X39,X40,X41) )
      & ( X37 = X41
        | k4_mcart_1(X34,X35,X36,X37) != k4_mcart_1(X38,X39,X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_mcart_1])])])).

cnf(c_0_25,negated_conjecture,
    ( esk5_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0) = esk13_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( X1 = k4_mcart_1(esk1_6(X2,X3,X4,X5,X1,X6),esk2_6(X2,X3,X4,X5,X1,X6),esk3_6(X2,X3,X4,X5,X1,X6),esk4_6(X2,X3,X4,X5,X1,X6))
    | X6 = k8_mcart_1(X2,X3,X4,X5,X1)
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | ~ m1_subset_1(X6,X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( X1 = X2
    | k4_mcart_1(X1,X3,X4,X5) != k4_mcart_1(X2,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k4_mcart_1(esk13_0,esk6_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk7_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk8_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)) = esk14_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k4_mcart_1(esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1),esk2_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1),esk3_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1),esk4_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1)) = esk14_0
    | X1 = k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)
    | ~ m1_subset_1(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk13_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk13_0 != k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,plain,
    ( X1 = k8_mcart_1(X2,X3,X4,X5,X6)
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 != esk1_6(X2,X3,X4,X5,X6,X1)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( esk13_0 = X1
    | k4_mcart_1(X1,X2,X3,X4) != esk14_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k4_mcart_1(esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0),esk2_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0),esk3_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0),esk4_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0)) = esk14_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)
    | esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1) != X1
    | ~ m1_subset_1(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0) = esk13_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t79_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_mcart_1)).
% 0.13/0.37  fof(l68_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&?[X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))&![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>![X9]:(m1_subset_1(X9,X4)=>X5!=k4_mcart_1(X6,X7,X8,X9)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 0.13/0.37  fof(d8_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>![X6]:(m1_subset_1(X6,X1)=>(X6=k8_mcart_1(X1,X2,X3,X4,X5)<=>![X7, X8, X9, X10]:(X5=k4_mcart_1(X7,X8,X9,X10)=>X6=X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_mcart_1)).
% 0.13/0.37  fof(t33_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 0.13/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t79_mcart_1])).
% 0.13/0.37  fof(c_0_5, plain, ![X25, X26, X27, X28, X29]:((m1_subset_1(esk5_5(X25,X26,X27,X28,X29),X25)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))&((m1_subset_1(esk6_5(X25,X26,X27,X28,X29),X26)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))&((m1_subset_1(esk7_5(X25,X26,X27,X28,X29),X27)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))&((m1_subset_1(esk8_5(X25,X26,X27,X28,X29),X28)|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0))&(X29=k4_mcart_1(esk5_5(X25,X26,X27,X28,X29),esk6_5(X25,X26,X27,X28,X29),esk7_5(X25,X26,X27,X28,X29),esk8_5(X25,X26,X27,X28,X29))|~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0|X28=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l68_mcart_1])])])])])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ![X48, X49, X50, X51]:(m1_subset_1(esk14_0,k4_zfmisc_1(esk9_0,esk10_0,esk11_0,esk12_0))&((~m1_subset_1(X48,esk9_0)|(~m1_subset_1(X49,esk10_0)|(~m1_subset_1(X50,esk11_0)|(~m1_subset_1(X51,esk12_0)|(esk14_0!=k4_mcart_1(X48,X49,X50,X51)|esk13_0=X48)))))&((((esk9_0!=k1_xboole_0&esk10_0!=k1_xboole_0)&esk11_0!=k1_xboole_0)&esk12_0!=k1_xboole_0)&esk13_0!=k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.13/0.37  cnf(c_0_7, plain, (X1=k4_mcart_1(esk5_5(X2,X3,X4,X5,X1),esk6_5(X2,X3,X4,X5,X1),esk7_5(X2,X3,X4,X5,X1),esk8_5(X2,X3,X4,X5,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk14_0,k4_zfmisc_1(esk9_0,esk10_0,esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (esk12_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (esk11_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_13, plain, (m1_subset_1(esk8_5(X1,X2,X3,X4,X5),X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_14, plain, (m1_subset_1(esk7_5(X1,X2,X3,X4,X5),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_15, plain, (m1_subset_1(esk6_5(X1,X2,X3,X4,X5),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_16, plain, (m1_subset_1(esk5_5(X1,X2,X3,X4,X5),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (esk13_0=X1|~m1_subset_1(X1,esk9_0)|~m1_subset_1(X2,esk10_0)|~m1_subset_1(X3,esk11_0)|~m1_subset_1(X4,esk12_0)|esk14_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (k4_mcart_1(esk5_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk6_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk7_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk8_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0))=esk14_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk8_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk12_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk11_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.13/0.37  fof(c_0_23, plain, ![X11, X12, X13, X14, X15, X16, X17, X18, X19, X20]:((X16!=k8_mcart_1(X11,X12,X13,X14,X15)|(X15!=k4_mcart_1(X17,X18,X19,X20)|X16=X17)|~m1_subset_1(X16,X11)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&((X15=k4_mcart_1(esk1_6(X11,X12,X13,X14,X15,X16),esk2_6(X11,X12,X13,X14,X15,X16),esk3_6(X11,X12,X13,X14,X15,X16),esk4_6(X11,X12,X13,X14,X15,X16))|X16=k8_mcart_1(X11,X12,X13,X14,X15)|~m1_subset_1(X16,X11)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0))&(X16!=esk1_6(X11,X12,X13,X14,X15,X16)|X16=k8_mcart_1(X11,X12,X13,X14,X15)|~m1_subset_1(X16,X11)|~m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))|(X11=k1_xboole_0|X12=k1_xboole_0|X13=k1_xboole_0|X14=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_mcart_1])])])])])])).
% 0.13/0.37  fof(c_0_24, plain, ![X34, X35, X36, X37, X38, X39, X40, X41]:((((X34=X38|k4_mcart_1(X34,X35,X36,X37)!=k4_mcart_1(X38,X39,X40,X41))&(X35=X39|k4_mcart_1(X34,X35,X36,X37)!=k4_mcart_1(X38,X39,X40,X41)))&(X36=X40|k4_mcart_1(X34,X35,X36,X37)!=k4_mcart_1(X38,X39,X40,X41)))&(X37=X41|k4_mcart_1(X34,X35,X36,X37)!=k4_mcart_1(X38,X39,X40,X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_mcart_1])])])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (esk5_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)=esk13_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.13/0.37  cnf(c_0_26, plain, (X1=k4_mcart_1(esk1_6(X2,X3,X4,X5,X1,X6),esk2_6(X2,X3,X4,X5,X1,X6),esk3_6(X2,X3,X4,X5,X1,X6),esk4_6(X2,X3,X4,X5,X1,X6))|X6=k8_mcart_1(X2,X3,X4,X5,X1)|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|~m1_subset_1(X6,X2)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_27, plain, (X1=X2|k4_mcart_1(X1,X3,X4,X5)!=k4_mcart_1(X2,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (k4_mcart_1(esk13_0,esk6_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk7_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0),esk8_5(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0))=esk14_0), inference(rw,[status(thm)],[c_0_18, c_0_25])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (k4_mcart_1(esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1),esk2_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1),esk3_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1),esk4_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1))=esk14_0|X1=k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)|~m1_subset_1(X1,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk13_0,esk9_0)), inference(rw,[status(thm)],[c_0_22, c_0_25])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (esk13_0!=k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_32, plain, (X1=k8_mcart_1(X2,X3,X4,X5,X6)|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k1_xboole_0|X1!=esk1_6(X2,X3,X4,X5,X6,X1)|~m1_subset_1(X1,X2)|~m1_subset_1(X6,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (esk13_0=X1|k4_mcart_1(X1,X2,X3,X4)!=esk14_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (k4_mcart_1(esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0),esk2_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0),esk3_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0),esk4_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0))=esk14_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (X1=k8_mcart_1(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0)|esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,X1)!=X1|~m1_subset_1(X1,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (esk1_6(esk9_0,esk10_0,esk11_0,esk12_0,esk14_0,esk13_0)=esk13_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30])]), c_0_31]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 38
% 0.13/0.37  # Proof object clause steps            : 29
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 24
% 0.13/0.37  # Proof object clause conjectures      : 21
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 15
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 12
% 0.13/0.37  # Proof object simplifying inferences  : 39
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 19
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 19
% 0.13/0.37  # Processed clauses                    : 59
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 4
% 0.13/0.37  # ...remaining for further processing  : 55
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.37  # Generated clauses                    : 46
% 0.13/0.37  # ...of the previous two non-trivial   : 44
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 41
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 6
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
% 0.13/0.37  # Current number of processed clauses  : 31
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 5
% 0.13/0.37  #    Non-unit-clauses                  : 18
% 0.13/0.37  # Current number of unprocessed clauses: 14
% 0.13/0.37  # ...number of literals in the above   : 40
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 23
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 116
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 37
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.37  # Unit Clause-clause subsumption calls : 9
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 4
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2599
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.032 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
