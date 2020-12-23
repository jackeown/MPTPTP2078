%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:10 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 373 expanded)
%              Number of clauses        :   26 ( 118 expanded)
%              Number of leaves         :    4 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  162 (2888 expanded)
%              Number of equality atoms :  109 (1759 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(l44_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ? [X4] :
            ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
            & ! [X5] :
                ( m1_subset_1(X5,X1)
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ! [X7] :
                        ( m1_subset_1(X7,X3)
                       => X4 != k3_mcart_1(X5,X6,X7) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

fof(d5_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( X5 = k5_mcart_1(X1,X2,X3,X4)
                  <=> ! [X6,X7,X8] :
                        ( X4 = k3_mcart_1(X6,X7,X8)
                       => X5 = X6 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_mcart_1)).

fof(t28_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_mcart_1(X1,X2,X3) = k3_mcart_1(X4,X5,X6)
     => ( X1 = X4
        & X2 = X5
        & X3 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

fof(c_0_4,negated_conjecture,(
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

fof(c_0_5,plain,(
    ! [X20,X21,X22,X23] :
      ( ( m1_subset_1(esk4_4(X20,X21,X22,X23),X20)
        | ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( m1_subset_1(esk5_4(X20,X21,X22,X23),X21)
        | ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( m1_subset_1(esk6_4(X20,X21,X22,X23),X22)
        | ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X23 = k3_mcart_1(esk4_4(X20,X21,X22,X23),esk5_4(X20,X21,X22,X23),esk6_4(X20,X21,X22,X23))
        | ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X38,X39,X40] :
      ( m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
      & ( ~ m1_subset_1(X38,esk7_0)
        | ~ m1_subset_1(X39,esk8_0)
        | ~ m1_subset_1(X40,esk9_0)
        | esk11_0 != k3_mcart_1(X38,X39,X40)
        | esk10_0 = X38 )
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k1_xboole_0
      & esk10_0 != k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( X1 = k3_mcart_1(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk6_4(X1,X2,X3,X4),X3)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),X2)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),X1)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( esk10_0 = X1
    | ~ m1_subset_1(X1,esk7_0)
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X3,esk9_0)
    | esk11_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( k3_mcart_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) = esk11_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_4(esk7_0,esk8_0,esk9_0,esk11_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( X13 != k5_mcart_1(X9,X10,X11,X12)
        | X12 != k3_mcart_1(X14,X15,X16)
        | X13 = X14
        | ~ m1_subset_1(X13,X9)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X12 = k3_mcart_1(esk1_5(X9,X10,X11,X12,X13),esk2_5(X9,X10,X11,X12,X13),esk3_5(X9,X10,X11,X12,X13))
        | X13 = k5_mcart_1(X9,X10,X11,X12)
        | ~ m1_subset_1(X13,X9)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X13 != esk1_5(X9,X10,X11,X12,X13)
        | X13 = k5_mcart_1(X9,X10,X11,X12)
        | ~ m1_subset_1(X13,X9)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_mcart_1])])])])])])).

fof(c_0_21,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( X27 = X30
        | k3_mcart_1(X27,X28,X29) != k3_mcart_1(X30,X31,X32) )
      & ( X28 = X31
        | k3_mcart_1(X27,X28,X29) != k3_mcart_1(X30,X31,X32) )
      & ( X29 = X32
        | k3_mcart_1(X27,X28,X29) != k3_mcart_1(X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).

cnf(c_0_22,negated_conjecture,
    ( esk4_4(esk7_0,esk8_0,esk9_0,esk11_0) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_23,plain,
    ( X1 = k3_mcart_1(esk1_5(X2,X3,X4,X1,X5),esk2_5(X2,X3,X4,X1,X5),esk3_5(X2,X3,X4,X1,X5))
    | X5 = k5_mcart_1(X2,X3,X4,X1)
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( X1 = X2
    | k3_mcart_1(X1,X3,X4) != k3_mcart_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k3_mcart_1(esk10_0,esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) = esk11_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,X1)) = esk11_0
    | X1 = k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk10_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk10_0 != k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,plain,
    ( X1 = k5_mcart_1(X2,X3,X4,X5)
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != esk1_5(X2,X3,X4,X5,X1)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( X1 = esk10_0
    | k3_mcart_1(X1,X2,X3) != esk11_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0)) = esk11_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)
    | esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,X1) != X1
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.013 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.13/0.36  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.13/0.36  fof(d5_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>![X5]:(m1_subset_1(X5,X1)=>(X5=k5_mcart_1(X1,X2,X3,X4)<=>![X6, X7, X8]:(X4=k3_mcart_1(X6,X7,X8)=>X5=X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_mcart_1)).
% 0.13/0.36  fof(t28_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_mcart_1(X1,X2,X3)=k3_mcart_1(X4,X5,X6)=>((X1=X4&X2=X5)&X3=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_mcart_1)).
% 0.13/0.36  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.13/0.36  fof(c_0_5, plain, ![X20, X21, X22, X23]:((m1_subset_1(esk4_4(X20,X21,X22,X23),X20)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((m1_subset_1(esk5_4(X20,X21,X22,X23),X21)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((m1_subset_1(esk6_4(X20,X21,X22,X23),X22)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&(X23=k3_mcart_1(esk4_4(X20,X21,X22,X23),esk5_4(X20,X21,X22,X23),esk6_4(X20,X21,X22,X23))|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.13/0.36  fof(c_0_6, negated_conjecture, ![X38, X39, X40]:(m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&((~m1_subset_1(X38,esk7_0)|(~m1_subset_1(X39,esk8_0)|(~m1_subset_1(X40,esk9_0)|(esk11_0!=k3_mcart_1(X38,X39,X40)|esk10_0=X38))))&(((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&esk9_0!=k1_xboole_0)&esk10_0!=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.13/0.36  cnf(c_0_7, plain, (X1=k3_mcart_1(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_9, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_10, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_11, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_12, plain, (m1_subset_1(esk6_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_13, plain, (m1_subset_1(esk5_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_14, plain, (m1_subset_1(esk4_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (esk10_0=X1|~m1_subset_1(X1,esk7_0)|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X3,esk9_0)|esk11_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_16, negated_conjecture, (k3_mcart_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))=esk11_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_4(esk7_0,esk8_0,esk9_0,esk11_0),esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.36  fof(c_0_20, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((X13!=k5_mcart_1(X9,X10,X11,X12)|(X12!=k3_mcart_1(X14,X15,X16)|X13=X14)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&((X12=k3_mcart_1(esk1_5(X9,X10,X11,X12,X13),esk2_5(X9,X10,X11,X12,X13),esk3_5(X9,X10,X11,X12,X13))|X13=k5_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&(X13!=esk1_5(X9,X10,X11,X12,X13)|X13=k5_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_mcart_1])])])])])])).
% 0.13/0.36  fof(c_0_21, plain, ![X27, X28, X29, X30, X31, X32]:(((X27=X30|k3_mcart_1(X27,X28,X29)!=k3_mcart_1(X30,X31,X32))&(X28=X31|k3_mcart_1(X27,X28,X29)!=k3_mcart_1(X30,X31,X32)))&(X29=X32|k3_mcart_1(X27,X28,X29)!=k3_mcart_1(X30,X31,X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).
% 0.13/0.36  cnf(c_0_22, negated_conjecture, (esk4_4(esk7_0,esk8_0,esk9_0,esk11_0)=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19])])).
% 0.13/0.36  cnf(c_0_23, plain, (X1=k3_mcart_1(esk1_5(X2,X3,X4,X1,X5),esk2_5(X2,X3,X4,X1,X5),esk3_5(X2,X3,X4,X1,X5))|X5=k5_mcart_1(X2,X3,X4,X1)|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.36  cnf(c_0_24, plain, (X1=X2|k3_mcart_1(X1,X3,X4)!=k3_mcart_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_25, negated_conjecture, (k3_mcart_1(esk10_0,esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))=esk11_0), inference(rw,[status(thm)],[c_0_16, c_0_22])).
% 0.13/0.36  cnf(c_0_26, negated_conjecture, (k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,X1))=esk11_0|X1=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)|~m1_subset_1(X1,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk10_0,esk7_0)), inference(rw,[status(thm)],[c_0_19, c_0_22])).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (esk10_0!=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_29, plain, (X1=k5_mcart_1(X2,X3,X4,X5)|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=esk1_5(X2,X3,X4,X5,X1)|~m1_subset_1(X1,X2)|~m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.36  cnf(c_0_30, negated_conjecture, (X1=esk10_0|k3_mcart_1(X1,X2,X3)!=esk11_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0))=esk11_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.13/0.36  cnf(c_0_32, negated_conjecture, (X1=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)|esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,X1)!=X1|~m1_subset_1(X1,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0)=esk10_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.36  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27])]), c_0_28]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 35
% 0.13/0.36  # Proof object clause steps            : 26
% 0.13/0.36  # Proof object formula steps           : 9
% 0.13/0.36  # Proof object conjectures             : 22
% 0.13/0.36  # Proof object clause conjectures      : 19
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 13
% 0.13/0.36  # Proof object initial formulas used   : 4
% 0.13/0.36  # Proof object generating inferences   : 11
% 0.13/0.36  # Proof object simplifying inferences  : 28
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 4
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 16
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 16
% 0.13/0.36  # Processed clauses                    : 51
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 3
% 0.13/0.36  # ...remaining for further processing  : 48
% 0.13/0.36  # Other redundant clauses eliminated   : 2
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 1
% 0.13/0.36  # Backward-rewritten                   : 3
% 0.13/0.36  # Generated clauses                    : 37
% 0.13/0.36  # ...of the previous two non-trivial   : 36
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 33
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 5
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 27
% 0.13/0.36  #    Positive orientable unit clauses  : 7
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 4
% 0.13/0.36  #    Non-unit-clauses                  : 16
% 0.13/0.36  # Current number of unprocessed clauses: 9
% 0.13/0.36  # ...number of literals in the above   : 20
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 20
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 62
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 25
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.36  # Unit Clause-clause subsumption calls : 30
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 4
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 2055
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.014 s
% 0.13/0.36  # System time              : 0.003 s
% 0.13/0.36  # Total time               : 0.017 s
% 0.13/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
