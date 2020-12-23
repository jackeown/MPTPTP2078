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
% DateTime   : Thu Dec  3 10:53:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  75 expanded)
%              Number of clauses        :   24 (  33 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 288 expanded)
%              Number of equality atoms :   60 ( 145 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_7,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X18,X19] : ~ r2_hidden(X18,k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,negated_conjecture,(
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

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X22),X20)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X20)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk3_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk4_2(X26,X27),esk3_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X39,X40] :
      ( ( ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40)
        | k1_relat_1(X39) != esk7_0
        | k1_relat_1(X40) != esk7_0
        | X39 = X40 )
      & esk7_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_15,plain,(
    ! [X35,X37] :
      ( v1_relat_1(esk6_1(X35))
      & v1_funct_1(esk6_1(X35))
      & k1_relat_1(esk6_1(X35)) = X35
      & ( ~ r2_hidden(X37,X35)
        | k1_funct_1(esk6_1(X35),X37) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_16,plain,(
    ! [X31,X32,X34] :
      ( v1_relat_1(esk5_2(X31,X32))
      & v1_funct_1(esk5_2(X31,X32))
      & k1_relat_1(esk5_2(X31,X32)) = X31
      & ( ~ r2_hidden(X34,X31)
        | k1_funct_1(esk5_2(X31,X32),X34) = X32 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_20,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk7_0
    | k1_relat_1(X2) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_relat_1(esk6_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk6_1(esk7_0)
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( k1_funct_1(esk6_1(X2),X1) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( k1_funct_1(esk5_2(X1,X2),esk3_2(k1_xboole_0,X1)) = X2
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( esk5_2(esk7_0,X1) = esk6_1(esk7_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])])).

cnf(c_0_33,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,plain,
    ( k1_funct_1(esk6_1(X1),esk3_2(k1_xboole_0,X1)) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk6_1(esk7_0),esk3_2(k1_xboole_0,esk7_0)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.048 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.13/0.40  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.13/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.13/0.40  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.13/0.40  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.13/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.40  fof(c_0_7, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.40  fof(c_0_8, plain, ![X18, X19]:~r2_hidden(X18,k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.13/0.40  cnf(c_0_9, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  fof(c_0_10, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.13/0.40  cnf(c_0_11, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_12, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.13/0.40  fof(c_0_13, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:(((~r2_hidden(X22,X21)|r2_hidden(k4_tarski(esk2_3(X20,X21,X22),X22),X20)|X21!=k2_relat_1(X20))&(~r2_hidden(k4_tarski(X25,X24),X20)|r2_hidden(X24,X21)|X21!=k2_relat_1(X20)))&((~r2_hidden(esk3_2(X26,X27),X27)|~r2_hidden(k4_tarski(X29,esk3_2(X26,X27)),X26)|X27=k2_relat_1(X26))&(r2_hidden(esk3_2(X26,X27),X27)|r2_hidden(k4_tarski(esk4_2(X26,X27),esk3_2(X26,X27)),X26)|X27=k2_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.13/0.40  fof(c_0_14, negated_conjecture, ![X39, X40]:((~v1_relat_1(X39)|~v1_funct_1(X39)|(~v1_relat_1(X40)|~v1_funct_1(X40)|(k1_relat_1(X39)!=esk7_0|k1_relat_1(X40)!=esk7_0|X39=X40)))&esk7_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X35, X37]:(((v1_relat_1(esk6_1(X35))&v1_funct_1(esk6_1(X35)))&k1_relat_1(esk6_1(X35))=X35)&(~r2_hidden(X37,X35)|k1_funct_1(esk6_1(X35),X37)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.13/0.40  fof(c_0_16, plain, ![X31, X32, X34]:(((v1_relat_1(esk5_2(X31,X32))&v1_funct_1(esk5_2(X31,X32)))&k1_relat_1(esk5_2(X31,X32))=X31)&(~r2_hidden(X34,X31)|k1_funct_1(esk5_2(X31,X32),X34)=X32)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.13/0.40  cnf(c_0_17, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.40  cnf(c_0_18, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_19, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk7_0|k1_relat_1(X2)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_21, plain, (v1_funct_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_22, plain, (k1_relat_1(esk6_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_23, plain, (v1_relat_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_24, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_25, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (X1=esk6_1(esk7_0)|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])])).
% 0.13/0.40  cnf(c_0_27, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_28, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_29, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_30, plain, (k1_funct_1(esk6_1(X2),X1)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_31, plain, (k1_funct_1(esk5_2(X1,X2),esk3_2(k1_xboole_0,X1))=X2|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (esk5_2(esk7_0,X1)=esk6_1(esk7_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_34, plain, (k1_funct_1(esk6_1(X1),esk3_2(k1_xboole_0,X1))=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk6_1(esk7_0),esk3_2(k1_xboole_0,esk7_0))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (X1=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_33])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_36])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 38
% 0.13/0.40  # Proof object clause steps            : 24
% 0.13/0.40  # Proof object formula steps           : 14
% 0.13/0.40  # Proof object conjectures             : 10
% 0.13/0.40  # Proof object clause conjectures      : 7
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 14
% 0.13/0.40  # Proof object initial formulas used   : 7
% 0.13/0.40  # Proof object generating inferences   : 8
% 0.13/0.40  # Proof object simplifying inferences  : 14
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 9
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 27
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 26
% 0.13/0.40  # Processed clauses                    : 70
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 2
% 0.13/0.40  # ...remaining for further processing  : 68
% 0.13/0.40  # Other redundant clauses eliminated   : 13
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 1
% 0.13/0.40  # Backward-rewritten                   : 26
% 0.13/0.40  # Generated clauses                    : 98
% 0.13/0.40  # ...of the previous two non-trivial   : 93
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 87
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 13
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 8
% 0.13/0.40  #    Positive orientable unit clauses  : 2
% 0.13/0.40  #    Positive unorientable unit clauses: 1
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 2
% 0.13/0.40  # Current number of unprocessed clauses: 57
% 0.13/0.40  # ...number of literals in the above   : 116
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 54
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 25
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 22
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.40  # Unit Clause-clause subsumption calls : 7
% 0.13/0.40  # Rewrite failures with RHS unbound    : 5
% 0.13/0.40  # BW rewrite match attempts            : 75
% 0.13/0.40  # BW rewrite match successes           : 71
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 2535
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.054 s
% 0.13/0.40  # System time              : 0.003 s
% 0.13/0.40  # Total time               : 0.057 s
% 0.13/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
