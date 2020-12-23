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
% DateTime   : Thu Dec  3 10:53:16 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   48 (1044 expanded)
%              Number of clauses        :   37 ( 371 expanded)
%              Number of leaves         :    5 ( 255 expanded)
%              Depth                    :   17
%              Number of atoms          :  152 (6072 expanded)
%              Number of equality atoms :   13 ( 197 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
            <=> ( r2_hidden(X1,k1_relat_1(X3))
                & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_funct_1])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))
      | ~ r2_hidden(esk3_0,k1_relat_1(esk5_0))
      | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0)) )
    & ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
      | r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0))) )
    & ( r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))
      | r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | k1_relat_1(k5_relat_1(X19,X20)) = k10_relat_1(X19,k1_relat_1(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X15] :
      ( ( r2_hidden(esk2_3(X11,X12,X13),k2_relat_1(X13))
        | ~ r2_hidden(X11,k10_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(X11,esk2_3(X11,X12,X13)),X13)
        | ~ r2_hidden(X11,k10_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X12)
        | ~ r2_hidden(X11,k10_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X15,k2_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X11,X15),X13)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X11,k10_relat_1(X13,X12))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k10_relat_1(X18,k2_relat_1(X18)) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(X21,k1_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X22 = k1_funct_1(X23,X21)
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X21,k1_relat_1(X23))
        | X22 != k1_funct_1(X23,X21)
        | r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))
    | r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0)),esk5_0)
    | r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X2),X2),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_12])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(X2),X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0),k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_12])])).

cnf(c_0_27,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_12])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk5_0,X2))
    | ~ r2_hidden(k4_tarski(X1,esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0)),esk5_0)
    | ~ r2_hidden(esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_12])])).

cnf(c_0_30,negated_conjecture,
    ( esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0) = k1_funct_1(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21]),c_0_12])])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk5_0,X2))
    | ~ r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,esk3_0)),esk5_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))
    | r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))
    | ~ r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))
    | r2_hidden(X1,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))
    | ~ r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,esk3_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk5_0,esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_21]),c_0_12])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_23])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))
    | r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_43]),c_0_12])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_43]),c_0_12])])).

cnf(c_0_46,negated_conjecture,
    ( esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0) = k1_funct_1(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_44]),c_0_21]),c_0_12])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:51:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.11/0.36  # and selection function SelectNewComplexAHPNS.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.028 s
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t21_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 0.11/0.36  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.11/0.36  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.11/0.36  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.11/0.36  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.11/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t21_funct_1])).
% 0.11/0.36  fof(c_0_6, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((~r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))|(~r2_hidden(esk3_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))))&((r2_hidden(esk3_0,k1_relat_1(esk5_0))|r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0))))&(r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))|r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.11/0.36  fof(c_0_7, plain, ![X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|k1_relat_1(k5_relat_1(X19,X20))=k10_relat_1(X19,k1_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.11/0.36  fof(c_0_8, plain, ![X11, X12, X13, X15]:((((r2_hidden(esk2_3(X11,X12,X13),k2_relat_1(X13))|~r2_hidden(X11,k10_relat_1(X13,X12))|~v1_relat_1(X13))&(r2_hidden(k4_tarski(X11,esk2_3(X11,X12,X13)),X13)|~r2_hidden(X11,k10_relat_1(X13,X12))|~v1_relat_1(X13)))&(r2_hidden(esk2_3(X11,X12,X13),X12)|~r2_hidden(X11,k10_relat_1(X13,X12))|~v1_relat_1(X13)))&(~r2_hidden(X15,k2_relat_1(X13))|~r2_hidden(k4_tarski(X11,X15),X13)|~r2_hidden(X15,X12)|r2_hidden(X11,k10_relat_1(X13,X12))|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.11/0.36  cnf(c_0_9, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))|r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_10, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.36  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  fof(c_0_13, plain, ![X18]:(~v1_relat_1(X18)|k10_relat_1(X18,k2_relat_1(X18))=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.11/0.36  fof(c_0_14, plain, ![X21, X22, X23]:(((r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X22=k1_funct_1(X23,X21)|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X21,k1_relat_1(X23))|X22!=k1_funct_1(X23,X21)|r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.11/0.36  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,esk2_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.36  cnf(c_0_16, negated_conjecture, (r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))|r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])])).
% 0.11/0.36  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.37  cnf(c_0_18, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_19, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0)),esk5_0)|r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])])).
% 0.11/0.37  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.37  cnf(c_0_22, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X2),X2),k2_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.11/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_12])])).
% 0.11/0.37  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,esk2_3(X1,k2_relat_1(X2),X2)),X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_15, c_0_18])).
% 0.11/0.37  cnf(c_0_25, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0),k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_12])])).
% 0.11/0.37  cnf(c_0_27, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_12])])).
% 0.11/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk5_0,X2))|~r2_hidden(k4_tarski(X1,esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0)),esk5_0)|~r2_hidden(esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_12])])).
% 0.11/0.37  cnf(c_0_30, negated_conjecture, (esk2_3(esk3_0,k2_relat_1(esk5_0),esk5_0)=k1_funct_1(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21]), c_0_12])])).
% 0.11/0.37  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk5_0,X2))|~r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,esk3_0)),esk5_0)|~r2_hidden(k1_funct_1(esk5_0,esk3_0),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30])).
% 0.11/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))|r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.37  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_31])).
% 0.11/0.37  cnf(c_0_35, negated_conjecture, (~r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))|~r2_hidden(esk3_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))|r2_hidden(X1,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))|~r2_hidden(k4_tarski(X1,k1_funct_1(esk5_0,esk3_0)),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.11/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk5_0,esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_21]), c_0_12])])).
% 0.11/0.37  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))|~r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_23])])).
% 0.11/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))|r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.11/0.37  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))|~r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_10]), c_0_11]), c_0_12])])).
% 0.11/0.37  cnf(c_0_41, negated_conjecture, (~r2_hidden(k1_funct_1(esk5_0,esk3_0),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.11/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk5_0,esk4_0)))), inference(sr,[status(thm)],[c_0_33, c_0_41])).
% 0.11/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_0,k10_relat_1(esk5_0,k1_relat_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_10]), c_0_11]), c_0_12])])).
% 0.11/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_43]), c_0_12])])).
% 0.11/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_43]), c_0_12])])).
% 0.11/0.37  cnf(c_0_46, negated_conjecture, (esk2_3(esk3_0,k1_relat_1(esk4_0),esk5_0)=k1_funct_1(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_44]), c_0_21]), c_0_12])])).
% 0.11/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_41]), ['proof']).
% 0.11/0.37  # SZS output end CNFRefutation
% 0.11/0.37  # Proof object total steps             : 48
% 0.11/0.37  # Proof object clause steps            : 37
% 0.11/0.37  # Proof object formula steps           : 11
% 0.11/0.37  # Proof object conjectures             : 29
% 0.11/0.37  # Proof object clause conjectures      : 26
% 0.11/0.37  # Proof object formula conjectures     : 3
% 0.11/0.37  # Proof object initial clauses used    : 14
% 0.11/0.37  # Proof object initial formulas used   : 5
% 0.11/0.37  # Proof object generating inferences   : 18
% 0.11/0.37  # Proof object simplifying inferences  : 42
% 0.11/0.37  # Training examples: 0 positive, 0 negative
% 0.11/0.37  # Parsed axioms                        : 7
% 0.11/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.37  # Initial clauses                      : 20
% 0.11/0.37  # Removed in clause preprocessing      : 0
% 0.11/0.37  # Initial clauses in saturation        : 20
% 0.11/0.37  # Processed clauses                    : 64
% 0.11/0.37  # ...of these trivial                  : 1
% 0.11/0.37  # ...subsumed                          : 4
% 0.11/0.37  # ...remaining for further processing  : 59
% 0.11/0.37  # Other redundant clauses eliminated   : 1
% 0.11/0.37  # Clauses deleted for lack of memory   : 0
% 0.11/0.37  # Backward-subsumed                    : 1
% 0.11/0.37  # Backward-rewritten                   : 20
% 0.11/0.37  # Generated clauses                    : 85
% 0.11/0.37  # ...of the previous two non-trivial   : 79
% 0.11/0.37  # Contextual simplify-reflections      : 1
% 0.11/0.37  # Paramodulations                      : 83
% 0.11/0.37  # Factorizations                       : 0
% 0.11/0.37  # Equation resolutions                 : 1
% 0.11/0.37  # Propositional unsat checks           : 0
% 0.11/0.37  #    Propositional check models        : 0
% 0.11/0.37  #    Propositional check unsatisfiable : 0
% 0.11/0.37  #    Propositional clauses             : 0
% 0.11/0.37  #    Propositional clauses after purity: 0
% 0.11/0.37  #    Propositional unsat core size     : 0
% 0.11/0.37  #    Propositional preprocessing time  : 0.000
% 0.11/0.37  #    Propositional encoding time       : 0.000
% 0.11/0.37  #    Propositional solver time         : 0.000
% 0.11/0.37  #    Success case prop preproc time    : 0.000
% 0.11/0.37  #    Success case prop encoding time   : 0.000
% 0.11/0.37  #    Success case prop solver time     : 0.000
% 0.11/0.37  # Current number of processed clauses  : 36
% 0.11/0.37  #    Positive orientable unit clauses  : 13
% 0.11/0.37  #    Positive unorientable unit clauses: 0
% 0.11/0.37  #    Negative unit clauses             : 1
% 0.11/0.37  #    Non-unit-clauses                  : 22
% 0.11/0.37  # Current number of unprocessed clauses: 32
% 0.11/0.37  # ...number of literals in the above   : 110
% 0.11/0.37  # Current number of archived formulas  : 0
% 0.11/0.37  # Current number of archived clauses   : 22
% 0.11/0.37  # Clause-clause subsumption calls (NU) : 100
% 0.11/0.37  # Rec. Clause-clause subsumption calls : 62
% 0.11/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.11/0.37  # Unit Clause-clause subsumption calls : 12
% 0.11/0.37  # Rewrite failures with RHS unbound    : 0
% 0.11/0.37  # BW rewrite match attempts            : 9
% 0.11/0.37  # BW rewrite match successes           : 5
% 0.11/0.37  # Condensation attempts                : 64
% 0.11/0.37  # Condensation successes               : 0
% 0.11/0.37  # Termbank termtop insertions          : 3159
% 0.11/0.37  
% 0.11/0.37  # -------------------------------------------------
% 0.11/0.37  # User time                : 0.032 s
% 0.11/0.37  # System time              : 0.003 s
% 0.11/0.37  # Total time               : 0.036 s
% 0.11/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
