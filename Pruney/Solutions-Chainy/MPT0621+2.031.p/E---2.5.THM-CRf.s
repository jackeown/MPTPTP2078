%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 235 expanded)
%              Number of clauses        :   27 ( 101 expanded)
%              Number of leaves         :    5 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 959 expanded)
%              Number of equality atoms :   67 ( 447 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
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

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

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

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X5] :
      ( ( k1_relat_1(X5) != k1_xboole_0
        | X5 = k1_xboole_0
        | ~ v1_relat_1(X5) )
      & ( k2_relat_1(X5) != k1_xboole_0
        | X5 = k1_xboole_0
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_7,plain,(
    ! [X16,X17,X19] :
      ( v1_relat_1(esk4_2(X16,X17))
      & v1_funct_1(esk4_2(X16,X17))
      & k1_relat_1(esk4_2(X16,X17)) = X16
      & ( ~ r2_hidden(X19,X16)
        | k1_funct_1(esk4_2(X16,X17),X19) = X17 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X24,X25] :
      ( ( ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | k1_relat_1(X24) != esk6_0
        | k1_relat_1(X25) != esk6_0
        | X24 = X25 )
      & esk6_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_9,plain,(
    ! [X20,X22] :
      ( v1_relat_1(esk5_1(X20))
      & v1_funct_1(esk5_1(X20))
      & k1_relat_1(esk5_1(X20)) = X20
      & ( ~ r2_hidden(X22,X20)
        | k1_funct_1(esk5_1(X20),X22) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_relat_1(esk4_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(esk4_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk6_0
    | k1_relat_1(X2) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk5_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_funct_1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k1_funct_1(esk4_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( esk4_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])])).

fof(c_0_19,plain,(
    ! [X6,X7,X8,X10,X11,X12,X14] :
      ( ( r2_hidden(esk1_3(X6,X7,X8),k1_relat_1(X6))
        | ~ r2_hidden(X8,X7)
        | X7 != k2_relat_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X8 = k1_funct_1(X6,esk1_3(X6,X7,X8))
        | ~ r2_hidden(X8,X7)
        | X7 != k2_relat_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(X11,k1_relat_1(X6))
        | X10 != k1_funct_1(X6,X11)
        | r2_hidden(X10,X7)
        | X7 != k2_relat_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk2_2(X6,X12),X12)
        | ~ r2_hidden(X14,k1_relat_1(X6))
        | esk2_2(X6,X12) != k1_funct_1(X6,X14)
        | X12 = k2_relat_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk3_2(X6,X12),k1_relat_1(X6))
        | r2_hidden(esk2_2(X6,X12),X12)
        | X12 = k2_relat_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk2_2(X6,X12) = k1_funct_1(X6,esk3_2(X6,X12))
        | r2_hidden(esk2_2(X6,X12),X12)
        | X12 = k2_relat_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk5_1(esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk4_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( k1_funct_1(k1_xboole_0,X1) = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk4_2(esk6_0,X1) = esk5_1(esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_11]),c_0_21]),c_0_12])])])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_22])).

cnf(c_0_26,plain,
    ( X1 = k2_relat_1(esk5_1(X2))
    | r2_hidden(esk2_2(esk5_1(X2),X1),X1)
    | r2_hidden(esk3_2(esk5_1(X2),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_14]),c_0_16])])).

cnf(c_0_27,plain,
    ( esk5_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_14]),c_0_16])])])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk5_1(esk6_0),X1) = X2
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | X2 = X3
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk6_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk6_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_33])])).

cnf(c_0_35,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( X1 = X2 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_35]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_29,c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.14/0.39  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.027 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 0.14/0.39  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.14/0.39  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.14/0.39  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.14/0.39  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.14/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.14/0.39  fof(c_0_6, plain, ![X5]:((k1_relat_1(X5)!=k1_xboole_0|X5=k1_xboole_0|~v1_relat_1(X5))&(k2_relat_1(X5)!=k1_xboole_0|X5=k1_xboole_0|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.14/0.39  fof(c_0_7, plain, ![X16, X17, X19]:(((v1_relat_1(esk4_2(X16,X17))&v1_funct_1(esk4_2(X16,X17)))&k1_relat_1(esk4_2(X16,X17))=X16)&(~r2_hidden(X19,X16)|k1_funct_1(esk4_2(X16,X17),X19)=X17)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.14/0.39  fof(c_0_8, negated_conjecture, ![X24, X25]:((~v1_relat_1(X24)|~v1_funct_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)|(k1_relat_1(X24)!=esk6_0|k1_relat_1(X25)!=esk6_0|X24=X25)))&esk6_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.14/0.39  fof(c_0_9, plain, ![X20, X22]:(((v1_relat_1(esk5_1(X20))&v1_funct_1(esk5_1(X20)))&k1_relat_1(esk5_1(X20))=X20)&(~r2_hidden(X22,X20)|k1_funct_1(esk5_1(X20),X22)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.14/0.39  cnf(c_0_10, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_11, plain, (k1_relat_1(esk4_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_12, plain, (v1_relat_1(esk4_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_13, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk6_0|k1_relat_1(X2)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_14, plain, (k1_relat_1(esk5_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_15, plain, (v1_funct_1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_16, plain, (v1_relat_1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_17, plain, (k1_funct_1(esk4_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_18, plain, (esk4_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])])).
% 0.14/0.39  fof(c_0_19, plain, ![X6, X7, X8, X10, X11, X12, X14]:((((r2_hidden(esk1_3(X6,X7,X8),k1_relat_1(X6))|~r2_hidden(X8,X7)|X7!=k2_relat_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(X8=k1_funct_1(X6,esk1_3(X6,X7,X8))|~r2_hidden(X8,X7)|X7!=k2_relat_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(~r2_hidden(X11,k1_relat_1(X6))|X10!=k1_funct_1(X6,X11)|r2_hidden(X10,X7)|X7!=k2_relat_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&((~r2_hidden(esk2_2(X6,X12),X12)|(~r2_hidden(X14,k1_relat_1(X6))|esk2_2(X6,X12)!=k1_funct_1(X6,X14))|X12=k2_relat_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((r2_hidden(esk3_2(X6,X12),k1_relat_1(X6))|r2_hidden(esk2_2(X6,X12),X12)|X12=k2_relat_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(esk2_2(X6,X12)=k1_funct_1(X6,esk3_2(X6,X12))|r2_hidden(esk2_2(X6,X12),X12)|X12=k2_relat_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (X1=esk5_1(esk6_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])])])).
% 0.14/0.39  cnf(c_0_21, plain, (v1_funct_1(esk4_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_22, plain, (k1_funct_1(k1_xboole_0,X1)=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.39  cnf(c_0_23, plain, (r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk2_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (esk4_2(esk6_0,X1)=esk5_1(esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_11]), c_0_21]), c_0_12])])])).
% 0.14/0.39  cnf(c_0_25, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_22])).
% 0.14/0.39  cnf(c_0_26, plain, (X1=k2_relat_1(esk5_1(X2))|r2_hidden(esk2_2(esk5_1(X2),X1),X1)|r2_hidden(esk3_2(esk5_1(X2),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_15]), c_0_14]), c_0_16])])).
% 0.14/0.39  cnf(c_0_27, plain, (esk5_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_14]), c_0_16])])])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk5_1(esk6_0),X1)=X2|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_24])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_30, plain, (X1=k2_relat_1(k1_xboole_0)|X2=X3|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_27])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, (X1=X2|~r2_hidden(X3,esk6_0)), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30])])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk6_0|X1=X2), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk6_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_33])])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (X1=esk6_0|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_32, c_0_34])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (X1=X2), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_35]), c_0_29])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_29, c_0_36]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 38
% 0.14/0.39  # Proof object clause steps            : 27
% 0.14/0.39  # Proof object formula steps           : 11
% 0.14/0.39  # Proof object conjectures             : 15
% 0.14/0.39  # Proof object clause conjectures      : 12
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 11
% 0.14/0.39  # Proof object initial formulas used   : 5
% 0.14/0.39  # Proof object generating inferences   : 14
% 0.14/0.39  # Proof object simplifying inferences  : 24
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 5
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 18
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 18
% 0.14/0.39  # Processed clauses                    : 170
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 71
% 0.14/0.39  # ...remaining for further processing  : 99
% 0.14/0.39  # Other redundant clauses eliminated   : 42
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 39
% 0.14/0.39  # Backward-rewritten                   : 14
% 0.14/0.39  # Generated clauses                    : 987
% 0.14/0.39  # ...of the previous two non-trivial   : 890
% 0.14/0.39  # Contextual simplify-reflections      : 2
% 0.14/0.39  # Paramodulations                      : 935
% 0.14/0.39  # Factorizations                       : 10
% 0.14/0.39  # Equation resolutions                 : 42
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 24
% 0.14/0.39  #    Positive orientable unit clauses  : 6
% 0.14/0.39  #    Positive unorientable unit clauses: 1
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 17
% 0.14/0.39  # Current number of unprocessed clauses: 588
% 0.14/0.39  # ...number of literals in the above   : 2053
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 72
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 571
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 526
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 79
% 0.14/0.39  # Unit Clause-clause subsumption calls : 59
% 0.14/0.39  # Rewrite failures with RHS unbound    : 130
% 0.14/0.39  # BW rewrite match attempts            : 126
% 0.14/0.39  # BW rewrite match successes           : 124
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 9279
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.041 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.046 s
% 0.14/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
