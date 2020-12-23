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

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 267 expanded)
%              Number of clauses        :   27 ( 116 expanded)
%              Number of leaves         :    6 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  117 (1037 expanded)
%              Number of equality atoms :   46 ( 417 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(s3_funct_1__e7_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,negated_conjecture,(
    ! [X37,X38] :
      ( ( ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38)
        | k1_relat_1(X37) != esk8_0
        | k1_relat_1(X38) != esk8_0
        | X37 = X38 )
      & esk8_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X33,X35] :
      ( v1_relat_1(esk7_1(X33))
      & v1_funct_1(esk7_1(X33))
      & k1_relat_1(esk7_1(X33)) = X33
      & ( ~ r2_hidden(X35,X33)
        | k1_funct_1(esk7_1(X33),X35) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

cnf(c_0_9,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk8_0
    | k1_relat_1(X2) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k1_relat_1(esk7_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( v1_funct_1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_relat_1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X29,X30,X32] :
      ( v1_relat_1(esk6_2(X29,X30))
      & v1_funct_1(esk6_2(X29,X30))
      & k1_relat_1(esk6_2(X29,X30)) = X29
      & ( ~ r2_hidden(X32,X29)
        | k1_funct_1(esk6_2(X29,X30),X32) = X30 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_14,negated_conjecture,
    ( X1 = esk7_1(esk8_0)
    | k1_relat_1(X1) != esk8_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])])).

cnf(c_0_15,plain,
    ( k1_relat_1(esk6_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( v1_funct_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( v1_relat_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_funct_1(esk6_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( esk6_2(esk8_0,X1) = esk7_1(esk8_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])])).

cnf(c_0_20,plain,
    ( k1_funct_1(esk7_1(X2),X1) = np__1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk7_1(esk8_0),X1) = X2
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( X1 = np__1
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(X20,esk3_3(X18,X19,X20)),X18)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X22,X23),X18)
        | r2_hidden(X22,X19)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(esk4_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(esk4_2(X24,X25),X27),X24)
        | X25 = k1_relat_1(X24) )
      & ( r2_hidden(esk4_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk4_2(X24,X25),esk5_2(X24,X25)),X24)
        | X25 = k1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( X1 = np__1
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( X1 = X2
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_31,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk4_2(X2,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k1_relat_1(esk8_0)
    | r2_hidden(esk4_2(esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k1_relat_1(esk8_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( X1 = esk8_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.024 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 0.19/0.42  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.19/0.42  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.19/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.42  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.42  fof(c_0_6, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.19/0.42  fof(c_0_7, negated_conjecture, ![X37, X38]:((~v1_relat_1(X37)|~v1_funct_1(X37)|(~v1_relat_1(X38)|~v1_funct_1(X38)|(k1_relat_1(X37)!=esk8_0|k1_relat_1(X38)!=esk8_0|X37=X38)))&esk8_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.19/0.42  fof(c_0_8, plain, ![X33, X35]:(((v1_relat_1(esk7_1(X33))&v1_funct_1(esk7_1(X33)))&k1_relat_1(esk7_1(X33))=X33)&(~r2_hidden(X35,X33)|k1_funct_1(esk7_1(X33),X35)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.19/0.42  cnf(c_0_9, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk8_0|k1_relat_1(X2)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_10, plain, (k1_relat_1(esk7_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_11, plain, (v1_funct_1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_12, plain, (v1_relat_1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  fof(c_0_13, plain, ![X29, X30, X32]:(((v1_relat_1(esk6_2(X29,X30))&v1_funct_1(esk6_2(X29,X30)))&k1_relat_1(esk6_2(X29,X30))=X29)&(~r2_hidden(X32,X29)|k1_funct_1(esk6_2(X29,X30),X32)=X30)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.19/0.42  cnf(c_0_14, negated_conjecture, (X1=esk7_1(esk8_0)|k1_relat_1(X1)!=esk8_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])])])).
% 0.19/0.42  cnf(c_0_15, plain, (k1_relat_1(esk6_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_16, plain, (v1_funct_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_17, plain, (v1_relat_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_18, plain, (k1_funct_1(esk6_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_19, negated_conjecture, (esk6_2(esk8_0,X1)=esk7_1(esk8_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])])).
% 0.19/0.42  cnf(c_0_20, plain, (k1_funct_1(esk7_1(X2),X1)=np__1|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_21, negated_conjecture, (k1_funct_1(esk7_1(esk8_0),X1)=X2|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.42  fof(c_0_22, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.42  cnf(c_0_23, negated_conjecture, (X1=np__1|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.42  cnf(c_0_24, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  fof(c_0_25, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(X20,esk3_3(X18,X19,X20)),X18)|X19!=k1_relat_1(X18))&(~r2_hidden(k4_tarski(X22,X23),X18)|r2_hidden(X22,X19)|X19!=k1_relat_1(X18)))&((~r2_hidden(esk4_2(X24,X25),X25)|~r2_hidden(k4_tarski(esk4_2(X24,X25),X27),X24)|X25=k1_relat_1(X24))&(r2_hidden(esk4_2(X24,X25),X25)|r2_hidden(k4_tarski(esk4_2(X24,X25),esk5_2(X24,X25)),X24)|X25=k1_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (X1=np__1|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.42  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_28, plain, (r2_hidden(esk4_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_29, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_30, negated_conjecture, (X1=X2|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.19/0.42  cnf(c_0_31, plain, (X1=k1_relat_1(X2)|r2_hidden(esk4_2(X2,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (v1_xboole_0(esk8_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30])])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (X1=k1_relat_1(esk8_0)|r2_hidden(esk4_2(esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (X1=k1_relat_1(esk8_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_33])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk8_0)=esk8_0), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (X1=esk8_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.42  cnf(c_0_37, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 39
% 0.19/0.42  # Proof object clause steps            : 27
% 0.19/0.42  # Proof object formula steps           : 12
% 0.19/0.42  # Proof object conjectures             : 17
% 0.19/0.42  # Proof object clause conjectures      : 14
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 14
% 0.19/0.42  # Proof object initial formulas used   : 6
% 0.19/0.42  # Proof object generating inferences   : 12
% 0.19/0.42  # Proof object simplifying inferences  : 11
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 7
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 23
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 23
% 0.19/0.42  # Processed clauses                    : 237
% 0.19/0.42  # ...of these trivial                  : 0
% 0.19/0.42  # ...subsumed                          : 55
% 0.19/0.42  # ...remaining for further processing  : 182
% 0.19/0.42  # Other redundant clauses eliminated   : 119
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 14
% 0.19/0.42  # Backward-rewritten                   : 16
% 0.19/0.42  # Generated clauses                    : 4672
% 0.19/0.42  # ...of the previous two non-trivial   : 4515
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 4541
% 0.19/0.42  # Factorizations                       : 14
% 0.19/0.42  # Equation resolutions                 : 119
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 124
% 0.19/0.42  #    Positive orientable unit clauses  : 15
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 9
% 0.19/0.42  #    Non-unit-clauses                  : 100
% 0.19/0.42  # Current number of unprocessed clauses: 3693
% 0.19/0.42  # ...number of literals in the above   : 11100
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 53
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 2709
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2408
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 40
% 0.19/0.42  # Unit Clause-clause subsumption calls : 159
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 63
% 0.19/0.42  # BW rewrite match successes           : 9
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 32545
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.067 s
% 0.19/0.42  # System time              : 0.006 s
% 0.19/0.42  # Total time               : 0.073 s
% 0.19/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
