%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:00 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 249 expanded)
%              Number of clauses        :   28 ( 126 expanded)
%              Number of leaves         :    7 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 852 expanded)
%              Number of equality atoms :   60 ( 391 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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

fof(s3_funct_1__e7_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

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

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X14,X15] : ~ r2_hidden(X14,k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(X18,esk3_3(X16,X17,X18)),X16)
        | X17 != k1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X16)
        | r2_hidden(X20,X17)
        | X17 != k1_relat_1(X16) )
      & ( ~ r2_hidden(esk4_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(esk4_2(X22,X23),X25),X22)
        | X23 = k1_relat_1(X22) )
      & ( r2_hidden(esk4_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk4_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_11,negated_conjecture,(
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

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,(
    ! [X37,X38] :
      ( ( ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38)
        | k1_relat_1(X37) != esk8_0
        | k1_relat_1(X38) != esk8_0
        | X37 = X38 )
      & esk8_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X33,X35] :
      ( v1_relat_1(esk7_1(X33))
      & v1_funct_1(esk7_1(X33))
      & k1_relat_1(esk7_1(X33)) = X33
      & ( ~ r2_hidden(X35,X33)
        | k1_funct_1(esk7_1(X33),X35) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk8_0
    | k1_relat_1(X2) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_relat_1(esk7_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v1_relat_1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X29,X30,X32] :
      ( v1_relat_1(esk6_2(X29,X30))
      & v1_funct_1(esk6_2(X29,X30))
      & k1_relat_1(esk6_2(X29,X30)) = X29
      & ( ~ r2_hidden(X32,X29)
        | k1_funct_1(esk6_2(X29,X30),X32) = X30 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(esk2_2(X9,X10),X9)
        | ~ r2_hidden(esk2_2(X9,X10),X10)
        | X9 = X10 )
      & ( r2_hidden(esk2_2(X9,X10),X9)
        | r2_hidden(esk2_2(X9,X10),X10)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk7_1(esk8_0)
    | k1_relat_1(X1) != esk8_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])])).

cnf(c_0_27,plain,
    ( k1_relat_1(esk6_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( v1_funct_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_relat_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_funct_1(esk6_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( esk6_2(esk8_0,X1) = esk7_1(esk8_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])])).

cnf(c_0_34,plain,
    ( k1_relat_1(k1_relat_1(k1_xboole_0)) = X1
    | r2_hidden(esk2_2(k1_relat_1(k1_relat_1(k1_xboole_0)),X1),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k1_funct_1(esk7_1(X2),X1) = np__1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk7_1(esk8_0),X1) = X2
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( X1 = np__1
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_37]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( X1 = np__1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:27:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.031 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.21/0.40  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.21/0.40  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.21/0.40  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.21/0.40  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.21/0.40  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.21/0.40  fof(c_0_7, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.40  fof(c_0_8, plain, ![X14, X15]:~r2_hidden(X14,k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.21/0.40  cnf(c_0_9, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.40  fof(c_0_10, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(X18,esk3_3(X16,X17,X18)),X16)|X17!=k1_relat_1(X16))&(~r2_hidden(k4_tarski(X20,X21),X16)|r2_hidden(X20,X17)|X17!=k1_relat_1(X16)))&((~r2_hidden(esk4_2(X22,X23),X23)|~r2_hidden(k4_tarski(esk4_2(X22,X23),X25),X22)|X23=k1_relat_1(X22))&(r2_hidden(esk4_2(X22,X23),X23)|r2_hidden(k4_tarski(esk4_2(X22,X23),esk5_2(X22,X23)),X22)|X23=k1_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.21/0.40  fof(c_0_11, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.21/0.40  cnf(c_0_12, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.40  cnf(c_0_13, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.21/0.40  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  fof(c_0_15, negated_conjecture, ![X37, X38]:((~v1_relat_1(X37)|~v1_funct_1(X37)|(~v1_relat_1(X38)|~v1_funct_1(X38)|(k1_relat_1(X37)!=esk8_0|k1_relat_1(X38)!=esk8_0|X37=X38)))&esk8_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.21/0.40  fof(c_0_16, plain, ![X33, X35]:(((v1_relat_1(esk7_1(X33))&v1_funct_1(esk7_1(X33)))&k1_relat_1(esk7_1(X33))=X33)&(~r2_hidden(X35,X33)|k1_funct_1(esk7_1(X33),X35)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.21/0.40  cnf(c_0_17, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.40  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk3_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_19, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk8_0|k1_relat_1(X2)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_20, plain, (k1_relat_1(esk7_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_21, plain, (v1_funct_1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_22, plain, (v1_relat_1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  fof(c_0_23, plain, ![X29, X30, X32]:(((v1_relat_1(esk6_2(X29,X30))&v1_funct_1(esk6_2(X29,X30)))&k1_relat_1(esk6_2(X29,X30))=X29)&(~r2_hidden(X32,X29)|k1_funct_1(esk6_2(X29,X30),X32)=X30)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.21/0.40  cnf(c_0_24, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.40  fof(c_0_25, plain, ![X9, X10]:((~r2_hidden(esk2_2(X9,X10),X9)|~r2_hidden(esk2_2(X9,X10),X10)|X9=X10)&(r2_hidden(esk2_2(X9,X10),X9)|r2_hidden(esk2_2(X9,X10),X10)|X9=X10)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (X1=esk7_1(esk8_0)|k1_relat_1(X1)!=esk8_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])])).
% 0.21/0.40  cnf(c_0_27, plain, (k1_relat_1(esk6_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_28, plain, (v1_funct_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_29, plain, (v1_relat_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_30, plain, (~r2_hidden(X1,k1_relat_1(k1_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.21/0.40  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_32, plain, (k1_funct_1(esk6_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (esk6_2(esk8_0,X1)=esk7_1(esk8_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])])).
% 0.21/0.40  cnf(c_0_34, plain, (k1_relat_1(k1_relat_1(k1_xboole_0))=X1|r2_hidden(esk2_2(k1_relat_1(k1_relat_1(k1_xboole_0)),X1),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.40  cnf(c_0_35, plain, (k1_funct_1(esk7_1(X2),X1)=np__1|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk7_1(esk8_0),X1)=X2|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.40  cnf(c_0_37, plain, (k1_relat_1(k1_relat_1(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_34])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (X1=np__1|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.40  cnf(c_0_39, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_37]), c_0_37])).
% 0.21/0.40  cnf(c_0_40, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_41, negated_conjecture, (X1=np__1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 43
% 0.21/0.40  # Proof object clause steps            : 28
% 0.21/0.40  # Proof object formula steps           : 15
% 0.21/0.40  # Proof object conjectures             : 11
% 0.21/0.40  # Proof object clause conjectures      : 8
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 14
% 0.21/0.40  # Proof object initial formulas used   : 7
% 0.21/0.40  # Proof object generating inferences   : 10
% 0.21/0.40  # Proof object simplifying inferences  : 15
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 11
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 26
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 26
% 0.21/0.40  # Processed clauses                    : 188
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 56
% 0.21/0.40  # ...remaining for further processing  : 132
% 0.21/0.40  # Other redundant clauses eliminated   : 16
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 1
% 0.21/0.40  # Backward-rewritten                   : 97
% 0.21/0.40  # Generated clauses                    : 998
% 0.21/0.40  # ...of the previous two non-trivial   : 964
% 0.21/0.40  # Contextual simplify-reflections      : 2
% 0.21/0.40  # Paramodulations                      : 972
% 0.21/0.40  # Factorizations                       : 10
% 0.21/0.40  # Equation resolutions                 : 16
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 4
% 0.21/0.40  #    Positive orientable unit clauses  : 1
% 0.21/0.40  #    Positive unorientable unit clauses: 1
% 0.21/0.40  #    Negative unit clauses             : 1
% 0.21/0.40  #    Non-unit-clauses                  : 1
% 0.21/0.40  # Current number of unprocessed clauses: 752
% 0.21/0.40  # ...number of literals in the above   : 1833
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 124
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 553
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 362
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 33
% 0.21/0.40  # Unit Clause-clause subsumption calls : 2
% 0.21/0.40  # Rewrite failures with RHS unbound    : 3
% 0.21/0.40  # BW rewrite match attempts            : 111
% 0.21/0.40  # BW rewrite match successes           : 48
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 9141
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.054 s
% 0.21/0.40  # System time              : 0.003 s
% 0.21/0.40  # Total time               : 0.057 s
% 0.21/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
