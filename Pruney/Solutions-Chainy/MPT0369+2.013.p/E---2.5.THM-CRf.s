%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:44 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   53 (  71 expanded)
%              Number of clauses        :   30 (  32 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 246 expanded)
%              Number of equality atoms :   34 (  49 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t50_subset_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(c_0_11,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk4_2(X32,X33),X33)
        | ~ r1_tarski(esk4_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk4_2(X32,X33),X33)
        | r1_tarski(esk4_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_12,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_13,plain,(
    ! [X40] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X40)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_14,plain,(
    ! [X39] : ~ v1_xboole_0(k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X1))
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ( ~ r2_hidden(X3,X2)
                 => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_subset_1])).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

fof(c_0_23,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk7_0,esk5_0)
    & ~ r2_hidden(esk7_0,esk6_0)
    & ~ r2_hidden(esk7_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k4_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_28,plain,(
    ! [X26,X27] : k4_xboole_0(X26,X27) = k5_xboole_0(X26,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,k1_xboole_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk7_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0)) = k3_subset_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.55/0.73  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.55/0.73  # and selection function SelectCQIArEqFirst.
% 0.55/0.73  #
% 0.55/0.73  # Preprocessing time       : 0.028 s
% 0.55/0.73  # Presaturation interreduction done
% 0.55/0.73  
% 0.55/0.73  # Proof found!
% 0.55/0.73  # SZS status Theorem
% 0.55/0.73  # SZS output start CNFRefutation
% 0.55/0.73  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.55/0.73  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.55/0.73  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.55/0.73  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.55/0.73  fof(t50_subset_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 0.55/0.73  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.55/0.73  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.55/0.73  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.55/0.73  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.55/0.73  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.55/0.73  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.55/0.73  fof(c_0_11, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk4_2(X32,X33),X33)|~r1_tarski(esk4_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk4_2(X32,X33),X33)|r1_tarski(esk4_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.55/0.73  fof(c_0_12, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.55/0.73  fof(c_0_13, plain, ![X40]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X40)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.55/0.73  fof(c_0_14, plain, ![X39]:~v1_xboole_0(k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.55/0.73  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.55/0.73  cnf(c_0_16, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.55/0.73  cnf(c_0_17, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.55/0.73  cnf(c_0_18, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.73  fof(c_0_19, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t50_subset_1])).
% 0.55/0.73  fof(c_0_20, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.55/0.73  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_15])).
% 0.55/0.73  cnf(c_0_22, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.55/0.73  fof(c_0_23, negated_conjecture, (esk5_0!=k1_xboole_0&(m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk7_0,esk5_0)&(~r2_hidden(esk7_0,esk6_0)&~r2_hidden(esk7_0,k3_subset_1(esk5_0,esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.55/0.73  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.55/0.73  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.55/0.73  fof(c_0_26, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.55/0.73  fof(c_0_27, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k4_xboole_0(X15,X16)))&((~r2_hidden(esk3_3(X20,X21,X22),X22)|(~r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k4_xboole_0(X20,X21))&((r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))&(~r2_hidden(esk3_3(X20,X21,X22),X21)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.55/0.73  fof(c_0_28, plain, ![X26, X27]:k4_xboole_0(X26,X27)=k5_xboole_0(X26,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.55/0.73  fof(c_0_29, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.55/0.73  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.55/0.73  cnf(c_0_31, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.55/0.73  cnf(c_0_32, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.55/0.73  cnf(c_0_33, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.55/0.73  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.55/0.73  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.55/0.73  cnf(c_0_36, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_30])).
% 0.55/0.73  cnf(c_0_37, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.55/0.73  cnf(c_0_38, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.55/0.73  fof(c_0_39, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.55/0.73  cnf(c_0_40, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.55/0.73  cnf(c_0_41, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.55/0.73  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_2(esk5_0,k1_xboole_0),esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.55/0.73  cnf(c_0_43, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.55/0.73  cnf(c_0_44, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.55/0.73  cnf(c_0_45, negated_conjecture, (r2_hidden(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.55/0.73  cnf(c_0_46, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_34])).
% 0.55/0.73  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.55/0.73  cnf(c_0_48, negated_conjecture, (r2_hidden(esk7_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.55/0.73  cnf(c_0_49, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0))=k3_subset_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.55/0.73  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk7_0,k3_subset_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.55/0.73  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.55/0.73  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), ['proof']).
% 0.55/0.73  # SZS output end CNFRefutation
% 0.55/0.73  # Proof object total steps             : 53
% 0.55/0.73  # Proof object clause steps            : 30
% 0.55/0.73  # Proof object formula steps           : 23
% 0.55/0.73  # Proof object conjectures             : 15
% 0.55/0.73  # Proof object clause conjectures      : 12
% 0.55/0.73  # Proof object formula conjectures     : 3
% 0.55/0.73  # Proof object initial clauses used    : 15
% 0.55/0.73  # Proof object initial formulas used   : 11
% 0.55/0.73  # Proof object generating inferences   : 11
% 0.55/0.73  # Proof object simplifying inferences  : 7
% 0.55/0.73  # Training examples: 0 positive, 0 negative
% 0.55/0.73  # Parsed axioms                        : 11
% 0.55/0.73  # Removed by relevancy pruning/SinE    : 0
% 0.55/0.73  # Initial clauses                      : 31
% 0.55/0.73  # Removed in clause preprocessing      : 1
% 0.55/0.73  # Initial clauses in saturation        : 30
% 0.55/0.73  # Processed clauses                    : 1294
% 0.55/0.73  # ...of these trivial                  : 10
% 0.55/0.73  # ...subsumed                          : 618
% 0.55/0.73  # ...remaining for further processing  : 666
% 0.55/0.73  # Other redundant clauses eliminated   : 11
% 0.55/0.73  # Clauses deleted for lack of memory   : 0
% 0.55/0.73  # Backward-subsumed                    : 31
% 0.55/0.73  # Backward-rewritten                   : 18
% 0.55/0.73  # Generated clauses                    : 38230
% 0.55/0.73  # ...of the previous two non-trivial   : 32149
% 0.55/0.73  # Contextual simplify-reflections      : 7
% 0.55/0.73  # Paramodulations                      : 38219
% 0.55/0.73  # Factorizations                       : 0
% 0.55/0.73  # Equation resolutions                 : 11
% 0.55/0.73  # Propositional unsat checks           : 0
% 0.55/0.73  #    Propositional check models        : 0
% 0.55/0.73  #    Propositional check unsatisfiable : 0
% 0.55/0.73  #    Propositional clauses             : 0
% 0.55/0.73  #    Propositional clauses after purity: 0
% 0.55/0.73  #    Propositional unsat core size     : 0
% 0.55/0.73  #    Propositional preprocessing time  : 0.000
% 0.55/0.73  #    Propositional encoding time       : 0.000
% 0.55/0.73  #    Propositional solver time         : 0.000
% 0.55/0.73  #    Success case prop preproc time    : 0.000
% 0.55/0.73  #    Success case prop encoding time   : 0.000
% 0.55/0.73  #    Success case prop solver time     : 0.000
% 0.55/0.73  # Current number of processed clauses  : 581
% 0.55/0.73  #    Positive orientable unit clauses  : 27
% 0.55/0.73  #    Positive unorientable unit clauses: 0
% 0.55/0.73  #    Negative unit clauses             : 22
% 0.55/0.73  #    Non-unit-clauses                  : 532
% 0.55/0.73  # Current number of unprocessed clauses: 30755
% 0.55/0.73  # ...number of literals in the above   : 135616
% 0.55/0.73  # Current number of archived formulas  : 0
% 0.55/0.73  # Current number of archived clauses   : 79
% 0.55/0.73  # Clause-clause subsumption calls (NU) : 114183
% 0.55/0.73  # Rec. Clause-clause subsumption calls : 78463
% 0.55/0.73  # Non-unit clause-clause subsumptions  : 489
% 0.55/0.73  # Unit Clause-clause subsumption calls : 509
% 0.55/0.73  # Rewrite failures with RHS unbound    : 0
% 0.55/0.73  # BW rewrite match attempts            : 14
% 0.55/0.73  # BW rewrite match successes           : 4
% 0.55/0.73  # Condensation attempts                : 0
% 0.55/0.73  # Condensation successes               : 0
% 0.55/0.73  # Termbank termtop insertions          : 584210
% 0.55/0.73  
% 0.55/0.73  # -------------------------------------------------
% 0.55/0.73  # User time                : 0.364 s
% 0.55/0.73  # System time              : 0.025 s
% 0.55/0.73  # Total time               : 0.390 s
% 0.55/0.73  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
