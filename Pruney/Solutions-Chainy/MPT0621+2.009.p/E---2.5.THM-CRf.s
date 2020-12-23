%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 395 expanded)
%              Number of clauses        :   25 ( 166 expanded)
%              Number of leaves         :    7 ( 111 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 (1254 expanded)
%              Number of equality atoms :   47 ( 425 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t16_funct_1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( k1_relat_1(X2) = X1
                  & k1_relat_1(X3) = X1 )
               => X2 = X3 ) ) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( r2_hidden(k4_tarski(esk2_4(X14,X15,X16,X17),X17),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_4(X14,X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X14)
        | ~ r2_hidden(X20,X15)
        | r2_hidden(X19,X16)
        | X16 != k9_relat_1(X14,X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(esk3_3(X14,X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk3_3(X14,X21,X22)),X14)
        | ~ r2_hidden(X24,X21)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk4_3(X14,X21,X22),esk3_3(X14,X21,X22)),X14)
        | r2_hidden(esk3_3(X14,X21,X22),X22)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk4_3(X14,X21,X22),X21)
        | r2_hidden(esk3_3(X14,X21,X22),X22)
        | X22 = k9_relat_1(X14,X21)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X30,X32] :
      ( v1_relat_1(esk6_1(X30))
      & v1_funct_1(esk6_1(X30))
      & k1_relat_1(esk6_1(X30)) = X30
      & ( ~ r2_hidden(X32,X30)
        | k1_funct_1(esk6_1(X30),X32) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_9,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X13] : r1_xboole_0(X13,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_11,plain,(
    ! [X12] : k3_xboole_0(X12,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_12,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_relat_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( k1_relat_1(X2) = X1
                    & k1_relat_1(X3) = X1 )
                 => X2 = X3 ) ) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t16_funct_1])).

cnf(c_0_18,plain,
    ( X1 = k9_relat_1(esk6_1(X2),X3)
    | r2_hidden(esk4_3(esk6_1(X2),X3,X1),X3)
    | r2_hidden(esk3_3(esk6_1(X2),X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

fof(c_0_20,negated_conjecture,(
    ! [X34,X35] :
      ( ( ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35)
        | k1_relat_1(X34) != esk7_0
        | k1_relat_1(X35) != esk7_0
        | X34 = X35 )
      & esk7_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

cnf(c_0_21,plain,
    ( k9_relat_1(esk6_1(X1),X2) = k1_xboole_0
    | r2_hidden(esk4_3(esk6_1(X1),X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_18]),c_0_16]),c_0_16]),c_0_16]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_3(esk6_1(X2),X3,k1_xboole_0),X3)
    | r2_hidden(esk3_3(esk6_1(X2),X3,X1),X1)
    | r2_hidden(esk4_3(esk6_1(X2),X3,X1),X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk7_0
    | k1_relat_1(X2) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_relat_1(esk6_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( v1_funct_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_27,plain,(
    ! [X26,X27,X29] :
      ( v1_relat_1(esk5_2(X26,X27))
      & v1_funct_1(esk5_2(X26,X27))
      & k1_relat_1(esk5_2(X26,X27)) = X26
      & ( ~ r2_hidden(X29,X26)
        | k1_funct_1(esk5_2(X26,X27),X29) = X27 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_3(esk6_1(X1),X2,esk7_0),esk7_0)
    | r2_hidden(esk4_3(esk6_1(X1),X2,esk7_0),X2)
    | r2_hidden(esk4_3(esk6_1(X1),X2,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( esk6_1(esk7_0) = X1
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_13])])])).

cnf(c_0_30,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k1_funct_1(esk6_1(X2),X1) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_3(esk6_1(X1),k1_xboole_0,esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_28]),c_0_19])).

cnf(c_0_35,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk5_2(esk7_0,X1) = esk6_1(esk7_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk6_1(esk7_0),esk3_3(esk6_1(X1),k1_xboole_0,esk7_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k1_xboole_0 = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_36]),c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_38]),c_0_38]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.39  # and selection function SelectNegativeLiterals.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.038 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 0.13/0.39  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.13/0.39  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.39  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.13/0.39  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.13/0.39  fof(c_0_7, plain, ![X14, X15, X16, X17, X19, X20, X21, X22, X24]:((((r2_hidden(k4_tarski(esk2_4(X14,X15,X16,X17),X17),X14)|~r2_hidden(X17,X16)|X16!=k9_relat_1(X14,X15)|~v1_relat_1(X14))&(r2_hidden(esk2_4(X14,X15,X16,X17),X15)|~r2_hidden(X17,X16)|X16!=k9_relat_1(X14,X15)|~v1_relat_1(X14)))&(~r2_hidden(k4_tarski(X20,X19),X14)|~r2_hidden(X20,X15)|r2_hidden(X19,X16)|X16!=k9_relat_1(X14,X15)|~v1_relat_1(X14)))&((~r2_hidden(esk3_3(X14,X21,X22),X22)|(~r2_hidden(k4_tarski(X24,esk3_3(X14,X21,X22)),X14)|~r2_hidden(X24,X21))|X22=k9_relat_1(X14,X21)|~v1_relat_1(X14))&((r2_hidden(k4_tarski(esk4_3(X14,X21,X22),esk3_3(X14,X21,X22)),X14)|r2_hidden(esk3_3(X14,X21,X22),X22)|X22=k9_relat_1(X14,X21)|~v1_relat_1(X14))&(r2_hidden(esk4_3(X14,X21,X22),X21)|r2_hidden(esk3_3(X14,X21,X22),X22)|X22=k9_relat_1(X14,X21)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.13/0.39  fof(c_0_8, plain, ![X30, X32]:(((v1_relat_1(esk6_1(X30))&v1_funct_1(esk6_1(X30)))&k1_relat_1(esk6_1(X30))=X30)&(~r2_hidden(X32,X30)|k1_funct_1(esk6_1(X30),X32)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.13/0.39  fof(c_0_9, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X13]:r1_xboole_0(X13,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.39  fof(c_0_11, plain, ![X12]:k3_xboole_0(X12,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.39  cnf(c_0_12, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_13, plain, (v1_relat_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_14, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_15, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.13/0.39  cnf(c_0_18, plain, (X1=k9_relat_1(esk6_1(X2),X3)|r2_hidden(esk4_3(esk6_1(X2),X3,X1),X3)|r2_hidden(esk3_3(esk6_1(X2),X3,X1),X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.39  cnf(c_0_19, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.13/0.39  fof(c_0_20, negated_conjecture, ![X34, X35]:((~v1_relat_1(X34)|~v1_funct_1(X34)|(~v1_relat_1(X35)|~v1_funct_1(X35)|(k1_relat_1(X34)!=esk7_0|k1_relat_1(X35)!=esk7_0|X34=X35)))&esk7_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.13/0.39  cnf(c_0_21, plain, (k9_relat_1(esk6_1(X1),X2)=k1_xboole_0|r2_hidden(esk4_3(esk6_1(X1),X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_18]), c_0_16]), c_0_16]), c_0_16]), c_0_19])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_23, plain, (X1=k1_xboole_0|r2_hidden(esk4_3(esk6_1(X2),X3,k1_xboole_0),X3)|r2_hidden(esk3_3(esk6_1(X2),X3,X1),X1)|r2_hidden(esk4_3(esk6_1(X2),X3,X1),X3)), inference(spm,[status(thm)],[c_0_18, c_0_21])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk7_0|k1_relat_1(X2)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_25, plain, (k1_relat_1(esk6_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_26, plain, (v1_funct_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  fof(c_0_27, plain, ![X26, X27, X29]:(((v1_relat_1(esk5_2(X26,X27))&v1_funct_1(esk5_2(X26,X27)))&k1_relat_1(esk5_2(X26,X27))=X26)&(~r2_hidden(X29,X26)|k1_funct_1(esk5_2(X26,X27),X29)=X27)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_3(esk6_1(X1),X2,esk7_0),esk7_0)|r2_hidden(esk4_3(esk6_1(X1),X2,esk7_0),X2)|r2_hidden(esk4_3(esk6_1(X1),X2,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (esk6_1(esk7_0)=X1|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_13])])])).
% 0.13/0.39  cnf(c_0_30, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_31, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_32, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_33, plain, (k1_funct_1(esk6_1(X2),X1)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_3(esk6_1(X1),k1_xboole_0,esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_28]), c_0_19])).
% 0.13/0.39  cnf(c_0_35, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (esk5_2(esk7_0,X1)=esk6_1(esk7_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk6_1(esk7_0),esk3_3(esk6_1(X1),k1_xboole_0,esk7_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (k1_xboole_0=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_36]), c_0_37])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_38]), c_0_38]), c_0_19]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 40
% 0.13/0.39  # Proof object clause steps            : 25
% 0.13/0.39  # Proof object formula steps           : 15
% 0.13/0.39  # Proof object conjectures             : 12
% 0.13/0.39  # Proof object clause conjectures      : 9
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 14
% 0.13/0.39  # Proof object initial formulas used   : 7
% 0.13/0.39  # Proof object generating inferences   : 10
% 0.13/0.39  # Proof object simplifying inferences  : 19
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 7
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 20
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 20
% 0.13/0.39  # Processed clauses                    : 70
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 10
% 0.13/0.39  # ...remaining for further processing  : 60
% 0.13/0.39  # Other redundant clauses eliminated   : 9
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 34
% 0.13/0.39  # Generated clauses                    : 145
% 0.13/0.39  # ...of the previous two non-trivial   : 149
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 136
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 9
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 3
% 0.13/0.39  #    Positive orientable unit clauses  : 1
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 0
% 0.13/0.39  # Current number of unprocessed clauses: 95
% 0.13/0.39  # ...number of literals in the above   : 416
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 54
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 76
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 23
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.39  # Unit Clause-clause subsumption calls : 6
% 0.13/0.39  # Rewrite failures with RHS unbound    : 3
% 0.13/0.39  # BW rewrite match attempts            : 47
% 0.13/0.39  # BW rewrite match successes           : 46
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 4129
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.047 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.051 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
