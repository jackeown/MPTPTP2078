%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 135 expanded)
%              Number of clauses        :   21 (  43 expanded)
%              Number of leaves         :    4 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  149 (1037 expanded)
%              Number of equality atoms :   93 ( 631 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   22 (   3 average)
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

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

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
    ! [X24,X25,X26,X27] :
      ( ( m1_subset_1(esk4_4(X24,X25,X26,X27),X24)
        | ~ m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 )
      & ( m1_subset_1(esk5_4(X24,X25,X26,X27),X25)
        | ~ m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 )
      & ( m1_subset_1(esk6_4(X24,X25,X26,X27),X26)
        | ~ m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 )
      & ( X27 = k3_mcart_1(esk4_4(X24,X25,X26,X27),esk5_4(X24,X25,X26,X27),esk6_4(X24,X25,X26,X27))
        | ~ m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X36,X37,X38] :
      ( m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
      & ( ~ m1_subset_1(X36,esk7_0)
        | ~ m1_subset_1(X37,esk8_0)
        | ~ m1_subset_1(X38,esk9_0)
        | esk11_0 != k3_mcart_1(X36,X37,X38)
        | esk10_0 = X36 )
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

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))
      | m1_subset_1(k5_mcart_1(X20,X21,X22,X23),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_17,negated_conjecture,
    ( esk10_0 = X1
    | ~ m1_subset_1(X1,esk7_0)
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X3,esk9_0)
    | esk11_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( k3_mcart_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) = esk11_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_4(esk7_0,esk8_0,esk9_0,esk11_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9]),c_0_10]),c_0_11])).

cnf(c_0_22,plain,
    ( X1 = X6
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 != k5_mcart_1(X2,X3,X4,X5)
    | X5 != k3_mcart_1(X6,X7,X8)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk4_4(esk7_0,esk8_0,esk9_0,esk11_0) = esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_25,plain,
    ( k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k3_mcart_1(esk10_0,esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0)) = esk11_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k5_mcart_1(X1,X2,X3,esk11_0) = esk10_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(esk11_0,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( esk10_0 != k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_8]),c_0_28]),c_0_9]),c_0_10]),c_0_11]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.20/0.38  fof(l44_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&?[X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>![X7]:(m1_subset_1(X7,X3)=>X4!=k3_mcart_1(X5,X6,X7))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 0.20/0.38  fof(d5_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>![X5]:(m1_subset_1(X5,X1)=>(X5=k5_mcart_1(X1,X2,X3,X4)<=>![X6, X7, X8]:(X4=k3_mcart_1(X6,X7,X8)=>X5=X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_mcart_1)).
% 0.20/0.38  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 0.20/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.20/0.38  fof(c_0_5, plain, ![X24, X25, X26, X27]:((m1_subset_1(esk4_4(X24,X25,X26,X27),X24)|~m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0))&((m1_subset_1(esk5_4(X24,X25,X26,X27),X25)|~m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0))&((m1_subset_1(esk6_4(X24,X25,X26,X27),X26)|~m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0))&(X27=k3_mcart_1(esk4_4(X24,X25,X26,X27),esk5_4(X24,X25,X26,X27),esk6_4(X24,X25,X26,X27))|~m1_subset_1(X27,k3_zfmisc_1(X24,X25,X26))|(X24=k1_xboole_0|X25=k1_xboole_0|X26=k1_xboole_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_mcart_1])])])])])).
% 0.20/0.38  fof(c_0_6, negated_conjecture, ![X36, X37, X38]:(m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&((~m1_subset_1(X36,esk7_0)|(~m1_subset_1(X37,esk8_0)|(~m1_subset_1(X38,esk9_0)|(esk11_0!=k3_mcart_1(X36,X37,X38)|esk10_0=X36))))&(((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&esk9_0!=k1_xboole_0)&esk10_0!=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.20/0.38  cnf(c_0_7, plain, (X1=k3_mcart_1(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1),esk6_4(X2,X3,X4,X1))|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_9, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_10, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_12, plain, (m1_subset_1(esk6_4(X1,X2,X3,X4),X3)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_13, plain, (m1_subset_1(esk5_4(X1,X2,X3,X4),X2)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_14, plain, (m1_subset_1(esk4_4(X1,X2,X3,X4),X1)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  fof(c_0_15, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((X13!=k5_mcart_1(X9,X10,X11,X12)|(X12!=k3_mcart_1(X14,X15,X16)|X13=X14)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&((X12=k3_mcart_1(esk1_5(X9,X10,X11,X12,X13),esk2_5(X9,X10,X11,X12,X13),esk3_5(X9,X10,X11,X12,X13))|X13=k5_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0))&(X13!=esk1_5(X9,X10,X11,X12,X13)|X13=k5_mcart_1(X9,X10,X11,X12)|~m1_subset_1(X13,X9)|~m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))|(X9=k1_xboole_0|X10=k1_xboole_0|X11=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_mcart_1])])])])])])).
% 0.20/0.38  fof(c_0_16, plain, ![X20, X21, X22, X23]:(~m1_subset_1(X23,k3_zfmisc_1(X20,X21,X22))|m1_subset_1(k5_mcart_1(X20,X21,X22,X23),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (esk10_0=X1|~m1_subset_1(X1,esk7_0)|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X3,esk9_0)|esk11_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (k3_mcart_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))=esk11_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_4(esk7_0,esk8_0,esk9_0,esk11_0),esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_4(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9]), c_0_10]), c_0_11])).
% 0.20/0.38  cnf(c_0_22, plain, (X1=X6|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X1!=k5_mcart_1(X2,X3,X4,X5)|X5!=k3_mcart_1(X6,X7,X8)|~m1_subset_1(X1,X2)|~m1_subset_1(X5,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_23, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (esk4_4(esk7_0,esk8_0,esk9_0,esk11_0)=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])])).
% 0.20/0.38  cnf(c_0_25, plain, (k5_mcart_1(X1,X2,X3,k3_mcart_1(X4,X5,X6))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X1,X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (k3_mcart_1(esk10_0,esk5_4(esk7_0,esk8_0,esk9_0,esk11_0),esk6_4(esk7_0,esk8_0,esk9_0,esk11_0))=esk11_0), inference(rw,[status(thm)],[c_0_18, c_0_24])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (k5_mcart_1(X1,X2,X3,esk11_0)=esk10_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(esk11_0,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (esk10_0!=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_8]), c_0_28]), c_0_9]), c_0_10]), c_0_11]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 30
% 0.20/0.38  # Proof object clause steps            : 21
% 0.20/0.38  # Proof object formula steps           : 9
% 0.20/0.38  # Proof object conjectures             : 17
% 0.20/0.38  # Proof object clause conjectures      : 14
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 4
% 0.20/0.38  # Proof object generating inferences   : 7
% 0.20/0.38  # Proof object simplifying inferences  : 24
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 4
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 14
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 14
% 0.20/0.38  # Processed clauses                    : 37
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 37
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 14
% 0.20/0.38  # ...of the previous two non-trivial   : 15
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 13
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 20
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 10
% 0.20/0.38  # Current number of unprocessed clauses: 6
% 0.20/0.38  # ...number of literals in the above   : 34
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 16
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 10
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 11
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1719
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.032 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
