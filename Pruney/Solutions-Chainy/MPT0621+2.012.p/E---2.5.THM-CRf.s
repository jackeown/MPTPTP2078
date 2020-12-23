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
% DateTime   : Thu Dec  3 10:53:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 100 expanded)
%              Number of clauses        :   24 (  44 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 370 expanded)
%              Number of equality atoms :   63 ( 183 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
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

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,negated_conjecture,(
    ! [X27,X28] :
      ( ( ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | k1_relat_1(X27) != esk5_0
        | k1_relat_1(X28) != esk5_0
        | X27 = X28 )
      & esk5_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X23,X25] :
      ( v1_relat_1(esk4_1(X23))
      & v1_funct_1(esk4_1(X23))
      & k1_relat_1(esk4_1(X23)) = X23
      & ( ~ r2_hidden(X25,X23)
        | k1_funct_1(esk4_1(X23),X25) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_10,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,k1_tarski(X18)) != X17
        | ~ r2_hidden(X18,X17) )
      & ( r2_hidden(X18,X17)
        | k4_xboole_0(X17,k1_tarski(X18)) = X17 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_12,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk5_0
    | k1_relat_1(X2) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_funct_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk4_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X19,X20,X22] :
      ( v1_relat_1(esk3_2(X19,X20))
      & v1_funct_1(esk3_2(X19,X20))
      & k1_relat_1(esk3_2(X19,X20)) = X19
      & ( ~ r2_hidden(X22,X19)
        | k1_funct_1(esk3_2(X19,X20),X22) = X20 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X8] : k4_xboole_0(k1_xboole_0,X8) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk4_1(X2)
    | k1_relat_1(X1) != esk5_0
    | X2 != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk3_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_relat_1(esk3_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk3_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_27,plain,
    ( k1_funct_1(esk3_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( esk3_2(X1,X2) = esk4_1(X3)
    | X1 != esk5_0
    | X3 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk4_1(X1),X2) = X3
    | X4 != esk5_0
    | X1 != esk5_0
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk4_1(X1),esk1_2(k1_xboole_0,X2)) = X3
    | k1_xboole_0 = X2
    | X2 != esk5_0
    | X1 != esk5_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( k1_xboole_0 = X1
    | X2 = X3
    | X1 != esk5_0
    | X4 != esk5_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( X1 = X2
    | X3 != esk5_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( X1 = X2 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_35,c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.038 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.20/0.40  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.20/0.40  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.20/0.40  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.40  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.20/0.40  fof(c_0_7, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.20/0.40  fof(c_0_8, negated_conjecture, ![X27, X28]:((~v1_relat_1(X27)|~v1_funct_1(X27)|(~v1_relat_1(X28)|~v1_funct_1(X28)|(k1_relat_1(X27)!=esk5_0|k1_relat_1(X28)!=esk5_0|X27=X28)))&esk5_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.20/0.40  fof(c_0_9, plain, ![X23, X25]:(((v1_relat_1(esk4_1(X23))&v1_funct_1(esk4_1(X23)))&k1_relat_1(esk4_1(X23))=X23)&(~r2_hidden(X25,X23)|k1_funct_1(esk4_1(X23),X25)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.20/0.40  fof(c_0_10, plain, ![X17, X18]:((k4_xboole_0(X17,k1_tarski(X18))!=X17|~r2_hidden(X18,X17))&(r2_hidden(X18,X17)|k4_xboole_0(X17,k1_tarski(X18))=X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.40  fof(c_0_11, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  cnf(c_0_12, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk5_0|k1_relat_1(X2)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_13, plain, (v1_funct_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_14, plain, (k1_relat_1(esk4_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_15, plain, (v1_relat_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  fof(c_0_16, plain, ![X19, X20, X22]:(((v1_relat_1(esk3_2(X19,X20))&v1_funct_1(esk3_2(X19,X20)))&k1_relat_1(esk3_2(X19,X20))=X19)&(~r2_hidden(X22,X19)|k1_funct_1(esk3_2(X19,X20),X22)=X20)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.20/0.40  cnf(c_0_17, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_19, plain, ![X8]:k4_xboole_0(k1_xboole_0,X8)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (X1=esk4_1(X2)|k1_relat_1(X1)!=esk5_0|X2!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])])).
% 0.20/0.40  cnf(c_0_21, plain, (v1_funct_1(esk3_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_22, plain, (k1_relat_1(esk3_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_23, plain, (v1_relat_1(esk3_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_24, plain, (k4_xboole_0(X1,k2_tarski(X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.40  cnf(c_0_25, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  fof(c_0_26, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.20/0.40  cnf(c_0_27, plain, (k1_funct_1(esk3_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (esk3_2(X1,X2)=esk4_1(X3)|X1!=esk5_0|X3!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.20/0.40  cnf(c_0_29, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.40  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk4_1(X1),X2)=X3|X4!=esk5_0|X1!=esk5_0|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.40  cnf(c_0_32, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (k1_funct_1(esk4_1(X1),esk1_2(k1_xboole_0,X2))=X3|k1_xboole_0=X2|X2!=esk5_0|X1!=esk5_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (k1_xboole_0=X1|X2=X3|X1!=esk5_0|X4!=esk5_0), inference(spm,[status(thm)],[c_0_33, c_0_33])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (X1=X2|X3!=esk5_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_35])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (X1=X2), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_35, c_0_37]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 39
% 0.20/0.40  # Proof object clause steps            : 24
% 0.20/0.40  # Proof object formula steps           : 15
% 0.20/0.40  # Proof object conjectures             : 13
% 0.20/0.40  # Proof object clause conjectures      : 10
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 13
% 0.20/0.40  # Proof object initial formulas used   : 7
% 0.20/0.40  # Proof object generating inferences   : 9
% 0.20/0.40  # Proof object simplifying inferences  : 9
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 8
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 20
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 19
% 0.20/0.40  # Processed clauses                    : 62
% 0.20/0.40  # ...of these trivial                  : 6
% 0.20/0.40  # ...subsumed                          : 11
% 0.20/0.40  # ...remaining for further processing  : 45
% 0.20/0.40  # Other redundant clauses eliminated   : 13
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 34
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 408
% 0.20/0.40  # ...of the previous two non-trivial   : 362
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 383
% 0.20/0.40  # Factorizations                       : 4
% 0.20/0.40  # Equation resolutions                 : 18
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 7
% 0.20/0.40  #    Positive orientable unit clauses  : 5
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 0
% 0.20/0.40  # Current number of unprocessed clauses: 316
% 0.20/0.40  # ...number of literals in the above   : 1694
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 38
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 162
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 87
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 22
% 0.20/0.40  # Unit Clause-clause subsumption calls : 32
% 0.20/0.40  # Rewrite failures with RHS unbound    : 64
% 0.20/0.40  # BW rewrite match attempts            : 47
% 0.20/0.40  # BW rewrite match successes           : 44
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 5679
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.054 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
