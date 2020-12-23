%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 132 expanded)
%              Number of clauses        :   34 (  61 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 342 expanded)
%              Number of equality atoms :   40 ( 111 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
        & ! [X6,X7,X8,X9] :
            ~ ( r2_hidden(X6,X2)
              & r2_hidden(X7,X3)
              & r2_hidden(X8,X4)
              & r2_hidden(X9,X5)
              & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(t72_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))
        & ! [X5,X6,X7] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & r2_hidden(X7,X4)
              & X1 = k3_mcart_1(X5,X6,X7) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
          & ! [X6,X7,X8,X9] :
              ~ ( r2_hidden(X6,X2)
                & r2_hidden(X7,X3)
                & r2_hidden(X8,X4)
                & r2_hidden(X9,X5)
                & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    inference(assume_negation,[status(cth)],[t83_mcart_1])).

fof(c_0_10,negated_conjecture,(
    ! [X46,X47,X48,X49] :
      ( r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0))
      & ( ~ r2_hidden(X46,esk7_0)
        | ~ r2_hidden(X47,esk8_0)
        | ~ r2_hidden(X48,esk9_0)
        | ~ r2_hidden(X49,esk10_0)
        | esk6_0 != k4_mcart_1(X46,X47,X48,X49) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26,X27] : k4_mcart_1(X24,X25,X26,X27) = k4_tarski(k4_tarski(k4_tarski(X24,X25),X26),X27) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

fof(c_0_12,plain,(
    ! [X32,X33,X34,X35] :
      ( ( r2_hidden(esk3_4(X32,X33,X34,X35),X33)
        | ~ r2_hidden(X32,k3_zfmisc_1(X33,X34,X35)) )
      & ( r2_hidden(esk4_4(X32,X33,X34,X35),X34)
        | ~ r2_hidden(X32,k3_zfmisc_1(X33,X34,X35)) )
      & ( r2_hidden(esk5_4(X32,X33,X34,X35),X35)
        | ~ r2_hidden(X32,k3_zfmisc_1(X33,X34,X35)) )
      & ( X32 = k3_mcart_1(esk3_4(X32,X33,X34,X35),esk4_4(X32,X33,X34,X35),esk5_4(X32,X33,X34,X35))
        | ~ r2_hidden(X32,k3_zfmisc_1(X33,X34,X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_mcart_1])])])])).

fof(c_0_13,plain,(
    ! [X15,X16,X17] : k3_mcart_1(X15,X16,X17) = k4_tarski(k4_tarski(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] : k3_zfmisc_1(X18,X19,X20) = k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X28,X29,X30,X31] : k4_zfmisc_1(X28,X29,X30,X31) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30),X31) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X4,esk10_0)
    | esk6_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = k3_mcart_1(esk3_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4),esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(X11,X12))
      | k4_tarski(esk1_1(X10),esk2_1(X10)) = X10 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ r2_hidden(X4,esk10_0)
    | ~ r2_hidden(X3,esk9_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( X1 = k4_tarski(k4_tarski(esk3_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4)),esk5_4(X1,X2,X3,X4))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_27,plain,(
    ! [X39,X40] :
      ( k1_mcart_1(k4_tarski(X39,X40)) = X39
      & k2_mcart_1(k4_tarski(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_28,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(esk5_4(X1,X3,X4,X5),esk9_0)
    | ~ r2_hidden(esk4_4(X1,X3,X4,X5),esk8_0)
    | ~ r2_hidden(esk3_4(X1,X3,X4,X5),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(esk1_1(esk6_0),esk2_1(esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(esk4_4(X1,X3,X4,esk9_0),esk8_0)
    | ~ r2_hidden(esk3_4(X1,X3,X4,esk9_0),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X3,X4),esk9_0))
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_20])).

cnf(c_0_37,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_38,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(k1_mcart_1(X21),X22)
        | ~ r2_hidden(X21,k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(k2_mcart_1(X21),X23)
        | ~ r2_hidden(X21,k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_39,negated_conjecture,
    ( esk1_1(esk6_0) = k1_mcart_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(esk3_4(X1,X3,esk8_0,esk9_0),esk7_0)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X3,esk8_0),esk9_0))
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_42,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk6_0),esk2_1(esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(X1,X2) != esk6_0
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( esk2_1(esk6_0) = k2_mcart_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk6_0),X1) != esk6_0
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk6_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:15:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.027 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t83_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 0.19/0.36  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.19/0.36  fof(t72_mcart_1, axiom, ![X1, X2, X3, X4]:~((r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))&![X5, X6, X7]:~((((r2_hidden(X5,X2)&r2_hidden(X6,X3))&r2_hidden(X7,X4))&X1=k3_mcart_1(X5,X6,X7))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_mcart_1)).
% 0.19/0.36  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.36  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.36  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.19/0.36  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.19/0.36  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.36  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.36  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9)))))), inference(assume_negation,[status(cth)],[t83_mcart_1])).
% 0.19/0.36  fof(c_0_10, negated_conjecture, ![X46, X47, X48, X49]:(r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0))&(~r2_hidden(X46,esk7_0)|~r2_hidden(X47,esk8_0)|~r2_hidden(X48,esk9_0)|~r2_hidden(X49,esk10_0)|esk6_0!=k4_mcart_1(X46,X47,X48,X49))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.19/0.36  fof(c_0_11, plain, ![X24, X25, X26, X27]:k4_mcart_1(X24,X25,X26,X27)=k4_tarski(k4_tarski(k4_tarski(X24,X25),X26),X27), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.19/0.36  fof(c_0_12, plain, ![X32, X33, X34, X35]:((((r2_hidden(esk3_4(X32,X33,X34,X35),X33)|~r2_hidden(X32,k3_zfmisc_1(X33,X34,X35)))&(r2_hidden(esk4_4(X32,X33,X34,X35),X34)|~r2_hidden(X32,k3_zfmisc_1(X33,X34,X35))))&(r2_hidden(esk5_4(X32,X33,X34,X35),X35)|~r2_hidden(X32,k3_zfmisc_1(X33,X34,X35))))&(X32=k3_mcart_1(esk3_4(X32,X33,X34,X35),esk4_4(X32,X33,X34,X35),esk5_4(X32,X33,X34,X35))|~r2_hidden(X32,k3_zfmisc_1(X33,X34,X35)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_mcart_1])])])])).
% 0.19/0.36  fof(c_0_13, plain, ![X15, X16, X17]:k3_mcart_1(X15,X16,X17)=k4_tarski(k4_tarski(X15,X16),X17), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.36  fof(c_0_14, plain, ![X18, X19, X20]:k3_zfmisc_1(X18,X19,X20)=k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.36  fof(c_0_15, plain, ![X28, X29, X30, X31]:k4_zfmisc_1(X28,X29,X30,X31)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30),X31), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.19/0.36  cnf(c_0_16, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X3,esk9_0)|~r2_hidden(X4,esk10_0)|esk6_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_17, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_18, plain, (X1=k3_mcart_1(esk3_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4),esk5_4(X1,X2,X3,X4))|~r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_19, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  cnf(c_0_20, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.36  fof(c_0_21, plain, ![X10, X11, X12]:(~r2_hidden(X10,k2_zfmisc_1(X11,X12))|k4_tarski(esk1_1(X10),esk2_1(X10))=X10), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.19/0.36  cnf(c_0_22, negated_conjecture, (r2_hidden(esk6_0,k4_zfmisc_1(esk7_0,esk8_0,esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_23, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.36  cnf(c_0_24, negated_conjecture, (esk6_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~r2_hidden(X4,esk10_0)|~r2_hidden(X3,esk9_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.36  cnf(c_0_25, plain, (X1=k4_tarski(k4_tarski(esk3_4(X1,X2,X3,X4),esk4_4(X1,X2,X3,X4)),esk5_4(X1,X2,X3,X4))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.36  cnf(c_0_26, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X4)|~r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  fof(c_0_27, plain, ![X39, X40]:(k1_mcart_1(k4_tarski(X39,X40))=X39&k2_mcart_1(k4_tarski(X39,X40))=X40), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.36  cnf(c_0_28, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.36  cnf(c_0_29, negated_conjecture, (r2_hidden(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),esk10_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.36  cnf(c_0_30, negated_conjecture, (k4_tarski(X1,X2)!=esk6_0|~r2_hidden(esk5_4(X1,X3,X4,X5),esk9_0)|~r2_hidden(esk4_4(X1,X3,X4,X5),esk8_0)|~r2_hidden(esk3_4(X1,X3,X4,X5),esk7_0)|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.36  cnf(c_0_31, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X4)|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_26, c_0_20])).
% 0.19/0.36  cnf(c_0_32, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_33, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.36  cnf(c_0_34, negated_conjecture, (k4_tarski(esk1_1(esk6_0),esk2_1(esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.36  cnf(c_0_35, negated_conjecture, (k4_tarski(X1,X2)!=esk6_0|~r2_hidden(esk4_4(X1,X3,X4,esk9_0),esk8_0)|~r2_hidden(esk3_4(X1,X3,X4,esk9_0),esk7_0)|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X3,X4),esk9_0))|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.36  cnf(c_0_36, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_32, c_0_20])).
% 0.19/0.36  cnf(c_0_37, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  fof(c_0_38, plain, ![X21, X22, X23]:((r2_hidden(k1_mcart_1(X21),X22)|~r2_hidden(X21,k2_zfmisc_1(X22,X23)))&(r2_hidden(k2_mcart_1(X21),X23)|~r2_hidden(X21,k2_zfmisc_1(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.36  cnf(c_0_39, negated_conjecture, (esk1_1(esk6_0)=k1_mcart_1(esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.36  cnf(c_0_40, negated_conjecture, (k4_tarski(X1,X2)!=esk6_0|~r2_hidden(esk3_4(X1,X3,esk8_0,esk9_0),esk7_0)|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X3,esk8_0),esk9_0))|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.36  cnf(c_0_41, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_37, c_0_20])).
% 0.19/0.36  cnf(c_0_42, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.36  cnf(c_0_43, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.36  cnf(c_0_44, negated_conjecture, (k4_tarski(k1_mcart_1(esk6_0),esk2_1(esk6_0))=esk6_0), inference(rw,[status(thm)],[c_0_34, c_0_39])).
% 0.19/0.36  cnf(c_0_45, negated_conjecture, (k4_tarski(X1,X2)!=esk6_0|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.36  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_42, c_0_29])).
% 0.19/0.36  cnf(c_0_47, negated_conjecture, (esk2_1(esk6_0)=k2_mcart_1(esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.36  cnf(c_0_48, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.36  cnf(c_0_49, negated_conjecture, (k4_tarski(k1_mcart_1(esk6_0),X1)!=esk6_0|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.36  cnf(c_0_50, negated_conjecture, (k4_tarski(k1_mcart_1(esk6_0),k2_mcart_1(esk6_0))=esk6_0), inference(rw,[status(thm)],[c_0_44, c_0_47])).
% 0.19/0.36  cnf(c_0_51, negated_conjecture, (r2_hidden(k2_mcart_1(esk6_0),esk10_0)), inference(spm,[status(thm)],[c_0_48, c_0_29])).
% 0.19/0.36  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 53
% 0.19/0.36  # Proof object clause steps            : 34
% 0.19/0.36  # Proof object formula steps           : 19
% 0.19/0.36  # Proof object conjectures             : 20
% 0.19/0.36  # Proof object clause conjectures      : 17
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 15
% 0.19/0.36  # Proof object initial formulas used   : 9
% 0.19/0.36  # Proof object generating inferences   : 11
% 0.19/0.36  # Proof object simplifying inferences  : 11
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 9
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 15
% 0.19/0.36  # Removed in clause preprocessing      : 4
% 0.19/0.36  # Initial clauses in saturation        : 11
% 0.19/0.36  # Processed clauses                    : 35
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 0
% 0.19/0.36  # ...remaining for further processing  : 35
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 2
% 0.19/0.36  # Generated clauses                    : 33
% 0.19/0.36  # ...of the previous two non-trivial   : 34
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 33
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 22
% 0.19/0.36  #    Positive orientable unit clauses  : 9
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 0
% 0.19/0.36  #    Non-unit-clauses                  : 13
% 0.19/0.36  # Current number of unprocessed clauses: 17
% 0.19/0.36  # ...number of literals in the above   : 39
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 17
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 15
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 0
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 2
% 0.19/0.36  # BW rewrite match successes           : 2
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 1700
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.029 s
% 0.19/0.36  # System time              : 0.003 s
% 0.19/0.36  # Total time               : 0.032 s
% 0.19/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
