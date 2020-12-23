%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:29 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  77 expanded)
%              Number of clauses        :   20 (  28 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :  140 ( 224 expanded)
%              Number of equality atoms :   84 ( 120 expanded)
%              Maximal formula depth    :   42 (   5 average)
%              Maximal clause size      :   60 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d5_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( X8 = k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X9 != X1
              & X9 != X2
              & X9 != X3
              & X9 != X4
              & X9 != X5
              & X9 != X6
              & X9 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19] : k3_enumset1(X16,X16,X17,X18,X19) = k2_enumset1(X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_16,plain,(
    ! [X20,X21,X22,X23,X24] : k4_enumset1(X20,X20,X21,X22,X23,X24) = k3_enumset1(X20,X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X28,X29,X30] : k5_enumset1(X25,X25,X26,X27,X28,X29,X30) = k4_enumset1(X25,X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_18,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37) = k5_enumset1(X31,X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_19,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55] :
      ( ( ~ r2_hidden(X46,X45)
        | X46 = X38
        | X46 = X39
        | X46 = X40
        | X46 = X41
        | X46 = X42
        | X46 = X43
        | X46 = X44
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X38
        | r2_hidden(X47,X45)
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X39
        | r2_hidden(X47,X45)
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X40
        | r2_hidden(X47,X45)
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X41
        | r2_hidden(X47,X45)
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X42
        | r2_hidden(X47,X45)
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X43
        | r2_hidden(X47,X45)
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( X47 != X44
        | r2_hidden(X47,X45)
        | X45 != k5_enumset1(X38,X39,X40,X41,X42,X43,X44) )
      & ( esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) != X48
        | ~ r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) )
      & ( esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) != X49
        | ~ r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) )
      & ( esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) != X50
        | ~ r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) )
      & ( esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) != X51
        | ~ r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) )
      & ( esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) != X52
        | ~ r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) )
      & ( esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) != X53
        | ~ r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) )
      & ( esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) != X54
        | ~ r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) )
      & ( r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)
        | esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) = X48
        | esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) = X49
        | esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) = X50
        | esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) = X51
        | esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) = X52
        | esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) = X53
        | esk1_8(X48,X49,X50,X51,X52,X53,X54,X55) = X54
        | X55 = k5_enumset1(X48,X49,X50,X51,X52,X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).

fof(c_0_20,plain,(
    ! [X57,X58,X59,X60] :
      ( ~ v1_funct_1(X60)
      | ~ v1_funct_2(X60,X57,X58)
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | ~ r2_hidden(X59,X57)
      | X58 = k1_xboole_0
      | r2_hidden(k1_funct_1(X60,X59),X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X5,X2,X6,X7,X8,X9) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk4_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X5,X2,X6,X7,X8,X9) ),
    inference(rw,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X3,X1,X4,X5,X6,X7)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(d5_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:(X8=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)<=>![X9]:(r2_hidden(X9,X8)<=>~(((((((X9!=X1&X9!=X2)&X9!=X3)&X9!=X4)&X9!=X5)&X9!=X6)&X9!=X7)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_enumset1)).
% 0.13/0.37  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.13/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.13/0.37  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.37  fof(c_0_12, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_13, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_14, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  fof(c_0_15, plain, ![X16, X17, X18, X19]:k3_enumset1(X16,X16,X17,X18,X19)=k2_enumset1(X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.37  fof(c_0_16, plain, ![X20, X21, X22, X23, X24]:k4_enumset1(X20,X20,X21,X22,X23,X24)=k3_enumset1(X20,X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.37  fof(c_0_17, plain, ![X25, X26, X27, X28, X29, X30]:k5_enumset1(X25,X25,X26,X27,X28,X29,X30)=k4_enumset1(X25,X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.37  fof(c_0_18, plain, ![X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37)=k5_enumset1(X31,X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.37  fof(c_0_19, plain, ![X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55]:(((~r2_hidden(X46,X45)|(X46=X38|X46=X39|X46=X40|X46=X41|X46=X42|X46=X43|X46=X44)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44))&(((((((X47!=X38|r2_hidden(X47,X45)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44))&(X47!=X39|r2_hidden(X47,X45)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44)))&(X47!=X40|r2_hidden(X47,X45)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44)))&(X47!=X41|r2_hidden(X47,X45)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44)))&(X47!=X42|r2_hidden(X47,X45)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44)))&(X47!=X43|r2_hidden(X47,X45)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44)))&(X47!=X44|r2_hidden(X47,X45)|X45!=k5_enumset1(X38,X39,X40,X41,X42,X43,X44))))&((((((((esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)!=X48|~r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54))&(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)!=X49|~r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54)))&(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)!=X50|~r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54)))&(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)!=X51|~r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54)))&(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)!=X52|~r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54)))&(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)!=X53|~r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54)))&(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)!=X54|~r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54)))&(r2_hidden(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55),X55)|(esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)=X48|esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)=X49|esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)=X50|esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)=X51|esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)=X52|esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)=X53|esk1_8(X48,X49,X50,X51,X52,X53,X54,X55)=X54)|X55=k5_enumset1(X48,X49,X50,X51,X52,X53,X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_enumset1])])])])])])).
% 0.13/0.37  fof(c_0_20, plain, ![X57, X58, X59, X60]:(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|(~r2_hidden(X59,X57)|(X58=k1_xboole_0|r2_hidden(k1_funct_1(X60,X59),X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_26, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_27, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_28, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X5,X2,X6,X7,X8,X9)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_31, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk4_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X5,X2,X6,X7,X8,X9)), inference(rw,[status(thm)],[c_0_30, c_0_28])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)|~r2_hidden(X1,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.13/0.37  cnf(c_0_38, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X3,X1,X4,X5,X6,X7))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (~r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 41
% 0.13/0.37  # Proof object clause steps            : 20
% 0.13/0.37  # Proof object formula steps           : 21
% 0.13/0.37  # Proof object conjectures             : 12
% 0.13/0.37  # Proof object clause conjectures      : 9
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 14
% 0.13/0.37  # Proof object initial formulas used   : 10
% 0.13/0.37  # Proof object generating inferences   : 2
% 0.13/0.37  # Proof object simplifying inferences  : 22
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 10
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 29
% 0.13/0.37  # Removed in clause preprocessing      : 7
% 0.13/0.37  # Initial clauses in saturation        : 22
% 0.13/0.37  # Processed clauses                    : 44
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 44
% 0.13/0.37  # Other redundant clauses eliminated   : 15
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 16
% 0.13/0.37  # ...of the previous two non-trivial   : 9
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 8
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 15
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
% 0.13/0.37  # Current number of processed clauses  : 14
% 0.13/0.37  #    Positive orientable unit clauses  : 10
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 2
% 0.13/0.37  # Current number of unprocessed clauses: 9
% 0.13/0.37  # ...number of literals in the above   : 38
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 29
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 42
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 42
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 42
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1845
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.028 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
