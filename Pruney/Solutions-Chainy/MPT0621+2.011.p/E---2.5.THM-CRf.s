%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 144 expanded)
%              Number of clauses        :   29 (  61 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 539 expanded)
%              Number of equality atoms :   53 ( 226 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(spc1_boole,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc1_boole)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,negated_conjecture,(
    ! [X25,X26] :
      ( ( ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | k1_relat_1(X25) != esk9_0
        | k1_relat_1(X26) != esk9_0
        | X25 = X26 )
      & esk9_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X21,X23] :
      ( v1_relat_1(esk8_1(X21))
      & v1_funct_1(esk8_1(X21))
      & k1_relat_1(esk8_1(X21)) = X21
      & ( ~ r2_hidden(X23,X21)
        | k1_funct_1(esk8_1(X21),X23) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

fof(c_0_11,plain,(
    ! [X18,X20] :
      ( v1_relat_1(esk7_1(X18))
      & v1_funct_1(esk7_1(X18))
      & k1_relat_1(esk7_1(X18)) = X18
      & ( ~ r2_hidden(X20,X18)
        | k1_funct_1(esk7_1(X18),X20) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X11,X13,X14] :
      ( ( ~ v1_relat_1(X7)
        | ~ r2_hidden(X8,X7)
        | X8 = k4_tarski(esk2_2(X7,X8),esk3_2(X7,X8)) )
      & ( r2_hidden(esk4_1(X11),X11)
        | v1_relat_1(X11) )
      & ( esk4_1(X11) != k4_tarski(X13,X14)
        | v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk9_0
    | k1_relat_1(X2) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk8_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_funct_1(esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | r2_hidden(k4_tarski(esk5_1(X15),esk6_1(X15)),X15)
      | X15 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_18,plain,
    ( k1_funct_1(esk7_1(X2),X1) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk8_1(esk9_0)
    | k1_relat_1(X1) != esk9_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk7_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( v1_funct_1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k1_funct_1(esk7_1(X1),esk4_1(X1)) = k1_xboole_0
    | v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( esk7_1(esk9_0) = esk8_1(esk9_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])])).

cnf(c_0_27,plain,
    ( k1_funct_1(esk8_1(X2),X1) = np__1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( k1_funct_1(esk7_1(X1),k4_tarski(esk5_1(X1),esk6_1(X1))) = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk8_1(esk9_0),esk4_1(esk9_0)) = k1_xboole_0
    | v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k1_funct_1(esk8_1(X1),esk4_1(X1)) = np__1
    | v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

fof(c_0_32,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_33,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk8_1(esk9_0),k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0))) = k1_xboole_0
    | ~ v1_relat_1(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( np__1 = k1_xboole_0
    | v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(fof_simplification,[status(thm)],[spc1_boole])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk8_1(esk9_0),k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0))) = k1_xboole_0
    | np__1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k1_funct_1(esk8_1(X1),k4_tarski(esk5_1(X1),esk6_1(X1))) = np__1
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_41,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(np__1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( np__1 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_29]),c_0_35])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_41])).

cnf(c_0_45,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S083N
% 0.20/0.39  # and selection function SelectCQArNT.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.040 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.20/0.39  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.20/0.39  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.20/0.39  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.20/0.39  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 0.20/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.39  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.20/0.39  fof(spc1_boole, axiom, ~(v1_xboole_0(np__1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', spc1_boole)).
% 0.20/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ![X25, X26]:((~v1_relat_1(X25)|~v1_funct_1(X25)|(~v1_relat_1(X26)|~v1_funct_1(X26)|(k1_relat_1(X25)!=esk9_0|k1_relat_1(X26)!=esk9_0|X25=X26)))&esk9_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.20/0.39  fof(c_0_10, plain, ![X21, X23]:(((v1_relat_1(esk8_1(X21))&v1_funct_1(esk8_1(X21)))&k1_relat_1(esk8_1(X21))=X21)&(~r2_hidden(X23,X21)|k1_funct_1(esk8_1(X21),X23)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.20/0.39  fof(c_0_11, plain, ![X18, X20]:(((v1_relat_1(esk7_1(X18))&v1_funct_1(esk7_1(X18)))&k1_relat_1(esk7_1(X18))=X18)&(~r2_hidden(X20,X18)|k1_funct_1(esk7_1(X18),X20)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.20/0.39  fof(c_0_12, plain, ![X7, X8, X11, X13, X14]:((~v1_relat_1(X7)|(~r2_hidden(X8,X7)|X8=k4_tarski(esk2_2(X7,X8),esk3_2(X7,X8))))&((r2_hidden(esk4_1(X11),X11)|v1_relat_1(X11))&(esk4_1(X11)!=k4_tarski(X13,X14)|v1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk9_0|k1_relat_1(X2)!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_14, plain, (k1_relat_1(esk8_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_15, plain, (v1_funct_1(esk8_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_16, plain, (v1_relat_1(esk8_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  fof(c_0_17, plain, ![X15]:(~v1_relat_1(X15)|(r2_hidden(k4_tarski(esk5_1(X15),esk6_1(X15)),X15)|X15=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.20/0.39  cnf(c_0_18, plain, (k1_funct_1(esk7_1(X2),X1)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_19, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (X1=esk8_1(esk9_0)|k1_relat_1(X1)!=esk9_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])])])).
% 0.20/0.39  cnf(c_0_21, plain, (k1_relat_1(esk7_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_22, plain, (v1_funct_1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_23, plain, (v1_relat_1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_24, plain, (r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_25, plain, (k1_funct_1(esk7_1(X1),esk4_1(X1))=k1_xboole_0|v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (esk7_1(esk9_0)=esk8_1(esk9_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])])).
% 0.20/0.39  cnf(c_0_27, plain, (k1_funct_1(esk8_1(X2),X1)=np__1|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_28, plain, (k1_funct_1(esk7_1(X1),k4_tarski(esk5_1(X1),esk6_1(X1)))=k1_xboole_0|X1=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_24])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk8_1(esk9_0),esk4_1(esk9_0))=k1_xboole_0|v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  cnf(c_0_31, plain, (k1_funct_1(esk8_1(X1),esk4_1(X1))=np__1|v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 0.20/0.39  fof(c_0_32, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.39  fof(c_0_33, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk8_1(esk9_0),k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)))=k1_xboole_0|~v1_relat_1(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_29])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (np__1=k1_xboole_0|v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.39  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_37, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  fof(c_0_38, plain, ~v1_xboole_0(np__1), inference(fof_simplification,[status(thm)],[spc1_boole])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk8_1(esk9_0),k4_tarski(esk5_1(esk9_0),esk6_1(esk9_0)))=k1_xboole_0|np__1=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.39  cnf(c_0_40, plain, (k1_funct_1(esk8_1(X1),k4_tarski(esk5_1(X1),esk6_1(X1)))=np__1|X1=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.20/0.39  cnf(c_0_41, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.39  cnf(c_0_42, plain, (~v1_xboole_0(np__1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (np__1=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_29]), c_0_35])).
% 0.20/0.39  cnf(c_0_44, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_37, c_0_41])).
% 0.20/0.39  cnf(c_0_45, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 46
% 0.20/0.39  # Proof object clause steps            : 29
% 0.20/0.39  # Proof object formula steps           : 17
% 0.20/0.39  # Proof object conjectures             : 12
% 0.20/0.39  # Proof object clause conjectures      : 9
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 15
% 0.20/0.39  # Proof object initial formulas used   : 8
% 0.20/0.39  # Proof object generating inferences   : 12
% 0.20/0.39  # Proof object simplifying inferences  : 15
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 8
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 17
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 17
% 0.20/0.39  # Processed clauses                    : 48
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 1
% 0.20/0.39  # ...remaining for further processing  : 47
% 0.20/0.39  # Other redundant clauses eliminated   : 4
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 7
% 0.20/0.39  # Generated clauses                    : 23
% 0.20/0.39  # ...of the previous two non-trivial   : 18
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 19
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 4
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 23
% 0.20/0.39  #    Positive orientable unit clauses  : 10
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 12
% 0.20/0.39  # Current number of unprocessed clauses: 1
% 0.20/0.39  # ...number of literals in the above   : 3
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 24
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 46
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 25
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.39  # Unit Clause-clause subsumption calls : 12
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1390
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.041 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.047 s
% 0.20/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
