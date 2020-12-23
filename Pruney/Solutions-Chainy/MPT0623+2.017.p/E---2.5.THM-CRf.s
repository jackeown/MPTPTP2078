%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:08 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 137 expanded)
%              Number of clauses        :   36 (  65 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 474 expanded)
%              Number of equality atoms :   82 ( 231 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X20] :
      ( ( k1_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) )
      & ( k2_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_13,plain,(
    ! [X21,X23] :
      ( v1_relat_1(esk3_1(X21))
      & v1_funct_1(esk3_1(X21))
      & k1_relat_1(esk3_1(X21)) = X21
      & ( ~ r2_hidden(X23,X21)
        | k1_funct_1(esk3_1(X21),X23) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X29] :
      ( ( esk5_0 != k1_xboole_0
        | esk6_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | esk6_0 != k1_relat_1(X29)
        | ~ r1_tarski(k2_relat_1(X29),esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ( v1_relat_1(esk4_2(X24,X25))
        | X24 = k1_xboole_0 )
      & ( v1_funct_1(esk4_2(X24,X25))
        | X24 = k1_xboole_0 )
      & ( k1_relat_1(esk4_2(X24,X25)) = X24
        | X24 = k1_xboole_0 )
      & ( k2_relat_1(esk4_2(X24,X25)) = k1_tarski(X25)
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_16,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_relat_1(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_relat_1(esk3_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk6_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_relat_1(esk4_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk4_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_funct_1(esk4_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( esk1_2(X1,X2) = X3
    | r1_tarski(X1,X2)
    | X1 != k1_tarski(X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_26,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_27,plain,
    ( esk3_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk4_2(X1,X2)) != esk6_0
    | ~ r1_tarski(k1_tarski(X2),esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_29,plain,
    ( k1_relat_1(esk4_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( esk1_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_33,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_27])).

cnf(c_0_36,plain,
    ( v1_funct_1(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 != esk6_0
    | ~ r1_tarski(k1_tarski(X2),esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( v1_funct_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

fof(c_0_42,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 != esk6_0
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_45,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k1_xboole_0
    | r1_tarski(esk5_0,X2)
    | X1 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:18:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.13/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.016 s
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.13/0.35  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.35  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.35  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.13/0.35  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.13/0.35  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.13/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.35  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.35  fof(c_0_9, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.13/0.35  fof(c_0_10, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.35  fof(c_0_11, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.35  fof(c_0_12, plain, ![X20]:((k1_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))&(k2_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.13/0.35  fof(c_0_13, plain, ![X21, X23]:(((v1_relat_1(esk3_1(X21))&v1_funct_1(esk3_1(X21)))&k1_relat_1(esk3_1(X21))=X21)&(~r2_hidden(X23,X21)|k1_funct_1(esk3_1(X21),X23)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.13/0.35  fof(c_0_14, negated_conjecture, ![X29]:((esk5_0!=k1_xboole_0|esk6_0=k1_xboole_0)&(~v1_relat_1(X29)|~v1_funct_1(X29)|(esk6_0!=k1_relat_1(X29)|~r1_tarski(k2_relat_1(X29),esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.13/0.35  fof(c_0_15, plain, ![X24, X25]:((((v1_relat_1(esk4_2(X24,X25))|X24=k1_xboole_0)&(v1_funct_1(esk4_2(X24,X25))|X24=k1_xboole_0))&(k1_relat_1(esk4_2(X24,X25))=X24|X24=k1_xboole_0))&(k2_relat_1(esk4_2(X24,X25))=k1_tarski(X25)|X24=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.13/0.35  cnf(c_0_16, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.35  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.35  cnf(c_0_18, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.35  cnf(c_0_19, plain, (v1_relat_1(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.35  cnf(c_0_20, plain, (k1_relat_1(esk3_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.35  cnf(c_0_21, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk6_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.35  cnf(c_0_22, plain, (k2_relat_1(esk4_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.35  cnf(c_0_23, plain, (v1_relat_1(esk4_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.35  cnf(c_0_24, plain, (v1_funct_1(esk4_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.35  cnf(c_0_25, plain, (esk1_2(X1,X2)=X3|r1_tarski(X1,X2)|X1!=k1_tarski(X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.35  fof(c_0_26, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.35  cnf(c_0_27, plain, (esk3_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.13/0.35  cnf(c_0_28, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk4_2(X1,X2))!=esk6_0|~r1_tarski(k1_tarski(X2),esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])).
% 0.13/0.35  cnf(c_0_29, plain, (k1_relat_1(esk4_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.35  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.35  cnf(c_0_31, plain, (esk1_2(k1_tarski(X1),X2)=X1|r1_tarski(k1_tarski(X1),X2)), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.35  cnf(c_0_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.35  cnf(c_0_33, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.35  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.35  cnf(c_0_35, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_27])).
% 0.13/0.35  cnf(c_0_36, plain, (v1_funct_1(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.35  cnf(c_0_37, negated_conjecture, (X1=k1_xboole_0|X1!=esk6_0|~r1_tarski(k1_tarski(X2),esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.35  cnf(c_0_38, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.35  cnf(c_0_39, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_32]), c_0_33]), c_0_34])])).
% 0.13/0.35  cnf(c_0_40, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_35])).
% 0.13/0.35  cnf(c_0_41, plain, (v1_funct_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.13/0.35  fof(c_0_42, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.35  cnf(c_0_43, negated_conjecture, (X1=k1_xboole_0|X1!=esk6_0|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.35  cnf(c_0_44, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.13/0.35  cnf(c_0_45, plain, (v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_41])).
% 0.13/0.35  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.35  cnf(c_0_47, negated_conjecture, (X1=k1_xboole_0|r1_tarski(esk5_0,X2)|X1!=esk6_0), inference(spm,[status(thm)],[c_0_43, c_0_17])).
% 0.13/0.35  cnf(c_0_48, negated_conjecture, (esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.13/0.35  cnf(c_0_49, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_34])).
% 0.13/0.35  cnf(c_0_50, negated_conjecture, (r1_tarski(esk5_0,X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48])).
% 0.13/0.35  cnf(c_0_51, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.35  cnf(c_0_52, negated_conjecture, (esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.35  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])]), c_0_48]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 54
% 0.13/0.35  # Proof object clause steps            : 36
% 0.13/0.35  # Proof object formula steps           : 18
% 0.13/0.35  # Proof object conjectures             : 15
% 0.13/0.35  # Proof object clause conjectures      : 12
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 17
% 0.13/0.35  # Proof object initial formulas used   : 9
% 0.13/0.35  # Proof object generating inferences   : 16
% 0.13/0.35  # Proof object simplifying inferences  : 14
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 9
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 25
% 0.13/0.35  # Removed in clause preprocessing      : 0
% 0.13/0.35  # Initial clauses in saturation        : 25
% 0.13/0.35  # Processed clauses                    : 56
% 0.13/0.35  # ...of these trivial                  : 2
% 0.13/0.35  # ...subsumed                          : 1
% 0.13/0.35  # ...remaining for further processing  : 53
% 0.13/0.35  # Other redundant clauses eliminated   : 3
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 1
% 0.13/0.35  # Backward-rewritten                   : 11
% 0.13/0.35  # Generated clauses                    : 49
% 0.13/0.35  # ...of the previous two non-trivial   : 45
% 0.13/0.35  # Contextual simplify-reflections      : 3
% 0.13/0.35  # Paramodulations                      : 39
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 10
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 38
% 0.13/0.35  #    Positive orientable unit clauses  : 11
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 1
% 0.13/0.35  #    Non-unit-clauses                  : 26
% 0.13/0.35  # Current number of unprocessed clauses: 10
% 0.13/0.35  # ...number of literals in the above   : 29
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 12
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 120
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 98
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.35  # Unit Clause-clause subsumption calls : 29
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 9
% 0.13/0.35  # BW rewrite match successes           : 4
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 1704
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.018 s
% 0.13/0.35  # System time              : 0.003 s
% 0.13/0.35  # Total time               : 0.021 s
% 0.13/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
