%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 130 expanded)
%              Number of clauses        :   27 (  53 expanded)
%              Number of leaves         :    6 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 601 expanded)
%              Number of equality atoms :   84 ( 344 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(t15_funct_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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
    ! [X24,X25] :
      ( ( ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | k1_relat_1(X24) != esk4_0
        | k1_relat_1(X25) != esk4_0
        | X24 = X25 )
      & esk4_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X20,X21] :
      ( ( v1_relat_1(esk3_2(X20,X21))
        | X20 = k1_xboole_0 )
      & ( v1_funct_1(esk3_2(X20,X21))
        | X20 = k1_xboole_0 )
      & ( k1_relat_1(esk3_2(X20,X21)) = X20
        | X20 = k1_xboole_0 )
      & ( k2_relat_1(esk3_2(X20,X21)) = k1_tarski(X21)
        | X20 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_9,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk4_0
    | k1_relat_1(X2) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k1_relat_1(esk3_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( X1 = esk3_2(esk4_0,X2)
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(esk3_2(esk4_0,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(esk3_2(esk4_0,X2))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10])]),c_0_11])).

cnf(c_0_13,plain,
    ( v1_funct_1(esk3_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk3_2(esk4_0,X2)
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(esk3_2(esk4_0,X2))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(esk3_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_19,plain,(
    ! [X17,X19] :
      ( v1_relat_1(esk2_1(X17))
      & v1_funct_1(esk2_1(X17))
      & k1_relat_1(esk2_1(X17)) = X17
      & ( ~ r2_hidden(X19,X17)
        | k1_funct_1(esk2_1(X17),X19) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

cnf(c_0_20,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_relat_1(esk3_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk3_2(esk4_0,X2)
    | k1_relat_1(X1) != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_11])).

cnf(c_0_25,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_funct_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(esk3_2(X1,X2)) = k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( esk3_2(esk4_0,X1) = esk2_1(esk4_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk2_1(esk4_0)) = k1_enumset1(X1,X1,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_11])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk2_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( X1 = X2 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_11,c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:49:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.13/0.37  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.13/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ![X24, X25]:((~v1_relat_1(X24)|~v1_funct_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)|(k1_relat_1(X24)!=esk4_0|k1_relat_1(X25)!=esk4_0|X24=X25)))&esk4_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X20, X21]:((((v1_relat_1(esk3_2(X20,X21))|X20=k1_xboole_0)&(v1_funct_1(esk3_2(X20,X21))|X20=k1_xboole_0))&(k1_relat_1(esk3_2(X20,X21))=X20|X20=k1_xboole_0))&(k2_relat_1(esk3_2(X20,X21))=k1_tarski(X21)|X20=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk4_0|k1_relat_1(X2)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, plain, (k1_relat_1(esk3_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (X1=esk3_2(esk4_0,X2)|k1_relat_1(X1)!=esk4_0|~v1_funct_1(esk3_2(esk4_0,X2))|~v1_funct_1(X1)|~v1_relat_1(esk3_2(esk4_0,X2))|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10])]), c_0_11])).
% 0.13/0.37  cnf(c_0_13, plain, (v1_funct_1(esk3_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_14, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_16, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (X1=esk3_2(esk4_0,X2)|k1_relat_1(X1)!=esk4_0|~v1_funct_1(X1)|~v1_relat_1(esk3_2(esk4_0,X2))|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_11])).
% 0.13/0.37  cnf(c_0_18, plain, (v1_relat_1(esk3_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_19, plain, ![X17, X19]:(((v1_relat_1(esk2_1(X17))&v1_funct_1(esk2_1(X17)))&k1_relat_1(esk2_1(X17))=X17)&(~r2_hidden(X19,X17)|k1_funct_1(esk2_1(X17),X19)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.13/0.37  cnf(c_0_20, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_relat_1(esk3_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (X1=esk3_2(esk4_0,X2)|k1_relat_1(X1)!=esk4_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_11])).
% 0.13/0.37  cnf(c_0_25, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_26, plain, (v1_funct_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_27, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_28, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_29, plain, (X1=k1_xboole_0|k2_relat_1(esk3_2(X1,X2))=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_21])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (esk3_2(esk4_0,X1)=esk2_1(esk4_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])])).
% 0.13/0.37  cnf(c_0_31, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk2_1(esk4_0))=k1_enumset1(X1,X1,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_11])).
% 0.13/0.37  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (X1=X2|~r2_hidden(X1,k2_relat_1(esk2_1(esk4_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.37  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_33, c_0_21])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (X1=X2|~r2_hidden(X1,k1_enumset1(X3,X3,X3))), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.13/0.37  cnf(c_0_37, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (X1=X2), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_11, c_0_38]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 40
% 0.13/0.37  # Proof object clause steps            : 27
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 14
% 0.13/0.37  # Proof object clause conjectures      : 11
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 8
% 0.13/0.37  # Proof object simplifying inferences  : 17
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 18
% 0.13/0.37  # Removed in clause preprocessing      : 2
% 0.13/0.37  # Initial clauses in saturation        : 16
% 0.13/0.37  # Processed clauses                    : 43
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 42
% 0.13/0.37  # Other redundant clauses eliminated   : 11
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 16
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 77
% 0.13/0.37  # ...of the previous two non-trivial   : 58
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 67
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 11
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
% 0.13/0.37  # Current number of processed clauses  : 5
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 1
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 46
% 0.13/0.37  # ...number of literals in the above   : 192
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 36
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 14
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 12
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.37  # Unit Clause-clause subsumption calls : 18
% 0.13/0.37  # Rewrite failures with RHS unbound    : 50
% 0.13/0.37  # BW rewrite match attempts            : 49
% 0.13/0.37  # BW rewrite match successes           : 42
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1816
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
