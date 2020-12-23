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
% DateTime   : Thu Dec  3 10:53:09 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   47 (  96 expanded)
%              Number of clauses        :   28 (  40 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 337 expanded)
%              Number of equality atoms :   56 ( 156 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
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

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

fof(c_0_9,negated_conjecture,(
    ! [X24] :
      ( ( esk4_0 != k1_xboole_0
        | esk5_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | esk5_0 != k1_relat_1(X24)
        | ~ r1_tarski(k2_relat_1(X24),esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X15] :
      ( ( k1_relat_1(X15) != k1_xboole_0
        | k2_relat_1(X15) = k1_xboole_0
        | ~ v1_relat_1(X15) )
      & ( k2_relat_1(X15) != k1_xboole_0
        | k1_relat_1(X15) = k1_xboole_0
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_11,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_12,plain,(
    ! [X19,X20] :
      ( ( v1_relat_1(esk3_2(X19,X20))
        | X19 = k1_xboole_0 )
      & ( v1_funct_1(esk3_2(X19,X20))
        | X19 = k1_xboole_0 )
      & ( k1_relat_1(esk3_2(X19,X20)) = X19
        | X19 = k1_xboole_0 )
      & ( k2_relat_1(esk3_2(X19,X20)) = k1_tarski(X20)
        | X19 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk5_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X16,X18] :
      ( v1_relat_1(esk2_1(X16))
      & v1_funct_1(esk2_1(X16))
      & k1_relat_1(esk2_1(X16)) = X16
      & ( ~ r2_hidden(X18,X16)
        | k1_funct_1(esk2_1(X16),X18) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

cnf(c_0_17,plain,
    ( k2_relat_1(esk3_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_relat_1(esk3_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_funct_1(esk3_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(X1) != esk5_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,
    ( ~ epred1_0
  <=> ! [X1] : X1 != esk5_0 ),
    introduced(definition)).

fof(c_0_25,plain,
    ( ~ epred2_0
  <=> ! [X2] : ~ r1_tarski(k1_tarski(X2),esk4_0) ),
    introduced(definition)).

cnf(c_0_26,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk3_2(X1,X2)) != esk5_0
    | ~ r1_tarski(k1_tarski(X2),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_27,plain,
    ( k1_relat_1(esk3_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( X1 != esk5_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_22]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( epred1_0
    | X1 != esk5_0 ),
    inference(split_equiv,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( epred1_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( ~ epred2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

fof(c_0_33,plain,(
    ! [X13,X14] :
      ( ( ~ r1_tarski(k1_tarski(X13),X14)
        | r2_hidden(X13,X14) )
      & ( ~ r2_hidden(X13,X14)
        | r1_tarski(k1_tarski(X13),X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_34,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(X1),esk4_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_25]),c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n017.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 17:04:16 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.32  # Version: 2.5pre002
% 0.16/0.32  # No SInE strategy applied
% 0.16/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.35  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.16/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.16/0.35  #
% 0.16/0.35  # Preprocessing time       : 0.027 s
% 0.16/0.35  
% 0.16/0.35  # Proof found!
% 0.16/0.35  # SZS status Theorem
% 0.16/0.35  # SZS output start CNFRefutation
% 0.16/0.35  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.16/0.35  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.16/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.16/0.35  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.16/0.35  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.16/0.35  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.16/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.35  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.16/0.35  fof(c_0_8, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.16/0.35  fof(c_0_9, negated_conjecture, ![X24]:((esk4_0!=k1_xboole_0|esk5_0=k1_xboole_0)&(~v1_relat_1(X24)|~v1_funct_1(X24)|(esk5_0!=k1_relat_1(X24)|~r1_tarski(k2_relat_1(X24),esk4_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.16/0.35  fof(c_0_10, plain, ![X15]:((k1_relat_1(X15)!=k1_xboole_0|k2_relat_1(X15)=k1_xboole_0|~v1_relat_1(X15))&(k2_relat_1(X15)!=k1_xboole_0|k1_relat_1(X15)=k1_xboole_0|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.16/0.35  fof(c_0_11, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.16/0.35  fof(c_0_12, plain, ![X19, X20]:((((v1_relat_1(esk3_2(X19,X20))|X19=k1_xboole_0)&(v1_funct_1(esk3_2(X19,X20))|X19=k1_xboole_0))&(k1_relat_1(esk3_2(X19,X20))=X19|X19=k1_xboole_0))&(k2_relat_1(esk3_2(X19,X20))=k1_tarski(X20)|X19=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.16/0.35  cnf(c_0_13, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk5_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.35  cnf(c_0_14, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.35  cnf(c_0_15, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.35  fof(c_0_16, plain, ![X16, X18]:(((v1_relat_1(esk2_1(X16))&v1_funct_1(esk2_1(X16)))&k1_relat_1(esk2_1(X16))=X16)&(~r2_hidden(X18,X16)|k1_funct_1(esk2_1(X16),X18)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.16/0.35  cnf(c_0_17, plain, (k2_relat_1(esk3_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.35  cnf(c_0_18, plain, (v1_relat_1(esk3_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.35  cnf(c_0_19, plain, (v1_funct_1(esk3_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.35  cnf(c_0_20, negated_conjecture, (k1_relat_1(X1)!=esk5_0|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.16/0.35  cnf(c_0_21, plain, (v1_funct_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.35  cnf(c_0_22, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.35  cnf(c_0_23, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.35  fof(c_0_24, plain, (~epred1_0<=>![X1]:X1!=esk5_0), introduced(definition)).
% 0.16/0.35  fof(c_0_25, plain, (~epred2_0<=>![X2]:~r1_tarski(k1_tarski(X2),esk4_0)), introduced(definition)).
% 0.16/0.35  cnf(c_0_26, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk3_2(X1,X2))!=esk5_0|~r1_tarski(k1_tarski(X2),esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_17]), c_0_18]), c_0_19])).
% 0.16/0.35  cnf(c_0_27, plain, (k1_relat_1(esk3_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.35  cnf(c_0_28, negated_conjecture, (X1!=esk5_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_22]), c_0_23])])).
% 0.16/0.35  cnf(c_0_29, negated_conjecture, (epred1_0|X1!=esk5_0), inference(split_equiv,[status(thm)],[c_0_24])).
% 0.16/0.35  cnf(c_0_30, negated_conjecture, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_24]), c_0_25])).
% 0.16/0.35  cnf(c_0_31, negated_conjecture, (epred1_0), inference(er,[status(thm)],[c_0_29])).
% 0.16/0.35  cnf(c_0_32, negated_conjecture, (~epred2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.16/0.35  fof(c_0_33, plain, ![X13, X14]:((~r1_tarski(k1_tarski(X13),X14)|r2_hidden(X13,X14))&(~r2_hidden(X13,X14)|r1_tarski(k1_tarski(X13),X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.16/0.35  fof(c_0_34, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.35  cnf(c_0_35, negated_conjecture, (~r1_tarski(k1_tarski(X1),esk4_0)), inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_25]), c_0_32])).
% 0.16/0.35  cnf(c_0_36, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.16/0.35  fof(c_0_37, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.16/0.35  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.16/0.35  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.16/0.35  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.35  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_15])).
% 0.16/0.35  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.16/0.35  cnf(c_0_43, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.35  cnf(c_0_44, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.16/0.35  cnf(c_0_45, negated_conjecture, (esk5_0!=k1_xboole_0), inference(er,[status(thm)],[c_0_28])).
% 0.16/0.35  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])]), c_0_45]), ['proof']).
% 0.16/0.35  # SZS output end CNFRefutation
% 0.16/0.35  # Proof object total steps             : 47
% 0.16/0.35  # Proof object clause steps            : 28
% 0.16/0.35  # Proof object formula steps           : 19
% 0.16/0.35  # Proof object conjectures             : 18
% 0.16/0.35  # Proof object clause conjectures      : 15
% 0.16/0.35  # Proof object formula conjectures     : 3
% 0.16/0.35  # Proof object initial clauses used    : 15
% 0.16/0.35  # Proof object initial formulas used   : 8
% 0.16/0.35  # Proof object generating inferences   : 10
% 0.16/0.35  # Proof object simplifying inferences  : 17
% 0.16/0.35  # Training examples: 0 positive, 0 negative
% 0.16/0.35  # Parsed axioms                        : 8
% 0.16/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.35  # Initial clauses                      : 21
% 0.16/0.35  # Removed in clause preprocessing      : 0
% 0.16/0.35  # Initial clauses in saturation        : 21
% 0.16/0.35  # Processed clauses                    : 52
% 0.16/0.35  # ...of these trivial                  : 2
% 0.16/0.35  # ...subsumed                          : 3
% 0.16/0.35  # ...remaining for further processing  : 47
% 0.16/0.35  # Other redundant clauses eliminated   : 2
% 0.16/0.35  # Clauses deleted for lack of memory   : 0
% 0.16/0.35  # Backward-subsumed                    : 3
% 0.16/0.35  # Backward-rewritten                   : 8
% 0.16/0.35  # Generated clauses                    : 50
% 0.16/0.35  # ...of the previous two non-trivial   : 46
% 0.16/0.35  # Contextual simplify-reflections      : 6
% 0.16/0.35  # Paramodulations                      : 43
% 0.16/0.35  # Factorizations                       : 0
% 0.16/0.35  # Equation resolutions                 : 4
% 0.16/0.35  # Propositional unsat checks           : 0
% 0.16/0.35  #    Propositional check models        : 0
% 0.16/0.35  #    Propositional check unsatisfiable : 0
% 0.16/0.35  #    Propositional clauses             : 0
% 0.16/0.35  #    Propositional clauses after purity: 0
% 0.16/0.35  #    Propositional unsat core size     : 0
% 0.16/0.35  #    Propositional preprocessing time  : 0.000
% 0.16/0.35  #    Propositional encoding time       : 0.000
% 0.16/0.35  #    Propositional solver time         : 0.000
% 0.16/0.35  #    Success case prop preproc time    : 0.000
% 0.16/0.35  #    Success case prop encoding time   : 0.000
% 0.16/0.35  #    Success case prop solver time     : 0.000
% 0.16/0.35  # Current number of processed clauses  : 33
% 0.16/0.35  #    Positive orientable unit clauses  : 8
% 0.16/0.35  #    Positive unorientable unit clauses: 0
% 0.16/0.35  #    Negative unit clauses             : 2
% 0.16/0.35  #    Non-unit-clauses                  : 23
% 0.16/0.35  # Current number of unprocessed clauses: 10
% 0.16/0.35  # ...number of literals in the above   : 27
% 0.16/0.35  # Current number of archived formulas  : 0
% 0.16/0.35  # Current number of archived clauses   : 11
% 0.16/0.35  # Clause-clause subsumption calls (NU) : 92
% 0.16/0.35  # Rec. Clause-clause subsumption calls : 78
% 0.16/0.35  # Non-unit clause-clause subsumptions  : 12
% 0.16/0.35  # Unit Clause-clause subsumption calls : 67
% 0.16/0.35  # Rewrite failures with RHS unbound    : 0
% 0.16/0.35  # BW rewrite match attempts            : 8
% 0.16/0.35  # BW rewrite match successes           : 2
% 0.16/0.35  # Condensation attempts                : 0
% 0.16/0.35  # Condensation successes               : 0
% 0.16/0.35  # Termbank termtop insertions          : 1602
% 0.16/0.35  
% 0.16/0.35  # -------------------------------------------------
% 0.16/0.35  # User time                : 0.029 s
% 0.16/0.35  # System time              : 0.004 s
% 0.16/0.35  # Total time               : 0.033 s
% 0.16/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
