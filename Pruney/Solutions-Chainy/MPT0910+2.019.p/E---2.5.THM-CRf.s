%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
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
fof(t70_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X7 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

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

fof(d6_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( X5 = k6_mcart_1(X1,X2,X3,X4)
                  <=> ! [X6,X7,X8] :
                        ( X4 = k3_mcart_1(X6,X7,X8)
                       => X5 = X7 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_mcart_1)).

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
                       => X4 = X7 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_mcart_1])).

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
        | esk10_0 = X39 )
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k1_xboole_0
      & esk10_0 != k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ) ),
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
    ( esk10_0 = X2
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
      ( ( X13 != k6_mcart_1(X9,X10,X11,X12)
        | X12 != k3_mcart_1(X14,X15,X16)
        | X13 = X15
        | ~ m1_subset_1(X13,X10)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X12 = k3_mcart_1(esk1_5(X9,X10,X11,X12,X13),esk2_5(X9,X10,X11,X12,X13),esk3_5(X9,X10,X11,X12,X13))
        | X13 = k6_mcart_1(X9,X10,X11,X12)
        | ~ m1_subset_1(X13,X10)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X13 != esk2_5(X9,X10,X11,X12,X13)
        | X13 = k6_mcart_1(X9,X10,X11,X12)
        | ~ m1_subset_1(X13,X10)
        | ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_mcart_1])])])])])])).

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
    ( esk5_4(esk7_0,esk8_0,esk9_0,esk11_0) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_23,plain,
    ( X1 = k3_mcart_1(esk1_5(X2,X3,X4,X1,X5),esk2_5(X2,X3,X4,X1,X5),esk3_5(X2,X3,X4,X1,X5))
    | X5 = k6_mcart_1(X2,X3,X4,X1)
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X5,X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( X1 = X2
    | k3_mcart_1(X3,X1,X4) != k3_mcart_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k3_mcart_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk10_0,esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) = esk11_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,X1)) = esk11_0
    | X1 = k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk10_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk10_0 != k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,plain,
    ( X1 = k6_mcart_1(X2,X3,X4,X5)
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != esk2_5(X2,X3,X4,X5,X1)
    | ~ m1_subset_1(X1,X3)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( esk10_0 = X1
    | k3_mcart_1(X2,X1,X3) != esk11_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0)) = esk11_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)
    | esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,X1) != X1
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:34:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t70_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_mcart_1)).
% 0.19/0.37  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.19/0.37  fof(d6_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>![X5]:(m1_subset_1(X5,X2)=>(X5=k6_mcart_1(X1,X2,X3,X4)<=>![X6, X7, X8]:(X4=k3_mcart_1(X6,X7,X8)=>X5=X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_mcart_1)).
% 0.19/0.37  fof(t28_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_mcart_1(X1,X2,X3)=k3_mcart_1(X4,X5,X6)=>((X1=X4&X2=X5)&X3=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_mcart_1)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t70_mcart_1])).
% 0.19/0.37  fof(c_0_5, plain, ![X20, X21, X22, X23]:((m1_subset_1(esk4_4(X20,X21,X22,X23),X20)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((m1_subset_1(esk5_4(X20,X21,X22,X23),X21)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&((m1_subset_1(esk6_4(X20,X21,X22,X23),X22)|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))&(X23=k3_mcart_1(esk4_4(X20,X21,X22,X23),esk5_4(X20,X21,X22,X23),esk6_4(X20,X21,X22,X23))|~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|(X20=k1_xboole_0|X21=k1_xboole_0|X22=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ![X38, X39, X40]:(m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&((~m1_subset_1(X38,esk7_0)|(~m1_subset_1(X39,esk8_0)|(~m1_subset_1(X40,esk9_0)|(esk11_0!=k3_mcart_1(X38,X39,X40)|esk10_0=X39))))&(((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&esk9_0!=k1_xboole_0)&esk10_0!=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.19/0.37  cnf(c_0_7, plain, (X1=k3_mcart_1(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_9, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_12, plain, (m1_subset_1(esk6_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_13, plain, (m1_subset_1(esk5_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_14, plain, (m1_subset_1(esk4_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (esk10_0=X2|~m1_subset_1(X1,esk7_0)|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X3,esk9_0)|esk11_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (k3_mcart_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))=esk11_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_4(esk7_0,esk8_0,esk9_0,esk11_0),esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.19/0.37  fof(c_0_20, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((X13!=k6_mcart_1(X9,X10,X11,X12)|(X12!=k3_mcart_1(X14,X15,X16)|X13=X15)|~m1_subset_1(X13,X10)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&((X12=k3_mcart_1(esk1_5(X9,X10,X11,X12,X13),esk2_5(X9,X10,X11,X12,X13),esk3_5(X9,X10,X11,X12,X13))|X13=k6_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X10)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&(X13!=esk2_5(X9,X10,X11,X12,X13)|X13=k6_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X10)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_mcart_1])])])])])])).
% 0.19/0.37  fof(c_0_21, plain, ![X27, X28, X29, X30, X31, X32]:(((X27=X30|k3_mcart_1(X27,X28,X29)!=k3_mcart_1(X30,X31,X32))&(X28=X31|k3_mcart_1(X27,X28,X29)!=k3_mcart_1(X30,X31,X32)))&(X29=X32|k3_mcart_1(X27,X28,X29)!=k3_mcart_1(X30,X31,X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_mcart_1])])])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (esk5_4(esk7_0,esk8_0,esk9_0,esk11_0)=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19])])).
% 0.19/0.37  cnf(c_0_23, plain, (X1=k3_mcart_1(esk1_5(X2,X3,X4,X1,X5),esk2_5(X2,X3,X4,X1,X5),esk3_5(X2,X3,X4,X1,X5))|X5=k6_mcart_1(X2,X3,X4,X1)|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X5,X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_24, plain, (X1=X2|k3_mcart_1(X3,X1,X4)!=k3_mcart_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (k3_mcart_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk10_0,esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))=esk11_0), inference(rw,[status(thm)],[c_0_16, c_0_22])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,X1),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,X1))=esk11_0|X1=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)|~m1_subset_1(X1,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk10_0,esk8_0)), inference(rw,[status(thm)],[c_0_18, c_0_22])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (esk10_0!=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_29, plain, (X1=k6_mcart_1(X2,X3,X4,X5)|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=esk2_5(X2,X3,X4,X5,X1)|~m1_subset_1(X1,X3)|~m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (esk10_0=X1|k3_mcart_1(X2,X1,X3)!=esk11_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (k3_mcart_1(esk1_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0),esk3_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0))=esk11_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (X1=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)|esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,X1)!=X1|~m1_subset_1(X1,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (esk2_5(esk7_0,esk8_0,esk9_0,esk11_0,esk10_0)=esk10_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27])]), c_0_28]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 35
% 0.19/0.37  # Proof object clause steps            : 26
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 22
% 0.19/0.37  # Proof object clause conjectures      : 19
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 28
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 51
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 3
% 0.19/0.37  # ...remaining for further processing  : 48
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 1
% 0.19/0.37  # Backward-rewritten                   : 3
% 0.19/0.37  # Generated clauses                    : 37
% 0.19/0.37  # ...of the previous two non-trivial   : 36
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 33
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 5
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 27
% 0.19/0.37  #    Positive orientable unit clauses  : 7
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 16
% 0.19/0.37  # Current number of unprocessed clauses: 9
% 0.19/0.37  # ...number of literals in the above   : 20
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 20
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 62
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 25
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.37  # Unit Clause-clause subsumption calls : 30
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 4
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2051
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
