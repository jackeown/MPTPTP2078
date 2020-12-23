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
% DateTime   : Thu Dec  3 10:56:12 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   53 (  93 expanded)
%              Number of clauses        :   32 (  43 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 266 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t30_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(t22_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r1_tarski(X1,X2)
                  & r2_hidden(X2,X3) )
               => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(c_0_10,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v1_ordinal1(X17)
        | ~ r2_hidden(X18,X17)
        | r1_tarski(X18,X17) )
      & ( r2_hidden(esk3_1(X19),X19)
        | v1_ordinal1(X19) )
      & ( ~ r1_tarski(esk3_1(X19),X19)
        | v1_ordinal1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_11,plain,(
    ! [X16] :
      ( ( v1_ordinal1(X16)
        | ~ v3_ordinal1(X16) )
      & ( v2_ordinal1(X16)
        | ~ v3_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t30_ordinal1])).

cnf(c_0_13,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & ~ v3_ordinal1(k3_tarski(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ( r2_hidden(esk2_2(X10,X11),X10)
        | r1_tarski(k3_tarski(X10),X11) )
      & ( ~ r1_tarski(esk2_2(X10,X11),X11)
        | r1_tarski(k3_tarski(X10),X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(k3_tarski(X13),X14)
      | ~ r2_hidden(X15,X13)
      | r1_tarski(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k3_tarski(X1),esk4_0)
    | ~ r2_hidden(esk2_2(X1,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_ordinal1(X22)
      | ~ v3_ordinal1(X23)
      | ~ v3_ordinal1(X24)
      | ~ r1_tarski(X22,X23)
      | ~ r2_hidden(X23,X24)
      | r2_hidden(X22,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ~ v3_ordinal1(X26)
      | ~ r2_hidden(X25,X26)
      | v3_ordinal1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k3_tarski(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k3_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk3_1(k3_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( v1_ordinal1(k3_tarski(esk4_0))
    | r2_hidden(esk3_1(k3_tarski(esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k3_tarski(esk4_0),X1)
    | ~ v1_ordinal1(k3_tarski(esk4_0))
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v1_ordinal1(k3_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k3_tarski(esk4_0),X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_46,plain,(
    ! [X27] :
      ( ~ v3_ordinal1(X27)
      | v3_ordinal1(k1_ordinal1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_44]),c_0_45])).

cnf(c_0_48,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_49,plain,(
    ! [X21] : r2_hidden(X21,k1_ordinal1(X21)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_50,negated_conjecture,
    ( ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk4_0,k1_ordinal1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:23:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.15/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.027 s
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.15/0.39  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.15/0.39  fof(t30_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 0.15/0.39  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.15/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.15/0.39  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.15/0.39  fof(t22_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r1_tarski(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 0.15/0.39  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.15/0.39  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.15/0.39  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.15/0.39  fof(c_0_10, plain, ![X17, X18, X19]:((~v1_ordinal1(X17)|(~r2_hidden(X18,X17)|r1_tarski(X18,X17)))&((r2_hidden(esk3_1(X19),X19)|v1_ordinal1(X19))&(~r1_tarski(esk3_1(X19),X19)|v1_ordinal1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.15/0.39  fof(c_0_11, plain, ![X16]:((v1_ordinal1(X16)|~v3_ordinal1(X16))&(v2_ordinal1(X16)|~v3_ordinal1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.15/0.39  fof(c_0_12, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t30_ordinal1])).
% 0.15/0.39  cnf(c_0_13, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  cnf(c_0_14, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.39  fof(c_0_15, negated_conjecture, (v3_ordinal1(esk4_0)&~v3_ordinal1(k3_tarski(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.15/0.39  fof(c_0_16, plain, ![X10, X11]:((r2_hidden(esk2_2(X10,X11),X10)|r1_tarski(k3_tarski(X10),X11))&(~r1_tarski(esk2_2(X10,X11),X11)|r1_tarski(k3_tarski(X10),X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.15/0.39  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.15/0.39  cnf(c_0_18, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  fof(c_0_19, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.15/0.39  cnf(c_0_20, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.39  cnf(c_0_21, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.15/0.39  fof(c_0_22, plain, ![X13, X14, X15]:(~r1_tarski(k3_tarski(X13),X14)|~r2_hidden(X15,X13)|r1_tarski(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.15/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.39  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.39  cnf(c_0_25, negated_conjecture, (r1_tarski(k3_tarski(X1),esk4_0)|~r2_hidden(esk2_2(X1,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.15/0.39  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.39  fof(c_0_27, plain, ![X22, X23, X24]:(~v1_ordinal1(X22)|(~v3_ordinal1(X23)|(~v3_ordinal1(X24)|(~r1_tarski(X22,X23)|~r2_hidden(X23,X24)|r2_hidden(X22,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).
% 0.15/0.39  fof(c_0_28, plain, ![X25, X26]:(~v3_ordinal1(X26)|(~r2_hidden(X25,X26)|v3_ordinal1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.15/0.39  cnf(c_0_29, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.39  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.39  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(k3_tarski(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.39  cnf(c_0_33, plain, (r2_hidden(X1,X3)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.39  cnf(c_0_34, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.15/0.39  cnf(c_0_35, plain, (v1_ordinal1(X1)|~r1_tarski(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  cnf(c_0_36, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k3_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.15/0.39  cnf(c_0_38, plain, (r2_hidden(esk3_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.39  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X3,X2)|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[c_0_33, c_0_34])).
% 0.15/0.39  cnf(c_0_40, plain, (v1_ordinal1(k3_tarski(X1))|~r2_hidden(esk3_1(k3_tarski(X1)),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.15/0.39  cnf(c_0_41, negated_conjecture, (v1_ordinal1(k3_tarski(esk4_0))|r2_hidden(esk3_1(k3_tarski(esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.15/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(k3_tarski(esk4_0),X1)|~v1_ordinal1(k3_tarski(esk4_0))|~v3_ordinal1(X1)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.15/0.39  cnf(c_0_43, negated_conjecture, (v1_ordinal1(k3_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.15/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(k3_tarski(esk4_0),X1)|~v3_ordinal1(X1)|~r2_hidden(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.15/0.39  cnf(c_0_45, negated_conjecture, (~v3_ordinal1(k3_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  fof(c_0_46, plain, ![X27]:(~v3_ordinal1(X27)|v3_ordinal1(k1_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.15/0.39  cnf(c_0_47, negated_conjecture, (~v3_ordinal1(X1)|~r2_hidden(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_44]), c_0_45])).
% 0.15/0.39  cnf(c_0_48, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.15/0.39  fof(c_0_49, plain, ![X21]:r2_hidden(X21,k1_ordinal1(X21)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.15/0.39  cnf(c_0_50, negated_conjecture, (~v3_ordinal1(X1)|~r2_hidden(esk4_0,k1_ordinal1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.15/0.39  cnf(c_0_51, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.15/0.39  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_18])]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 53
% 0.15/0.39  # Proof object clause steps            : 32
% 0.15/0.39  # Proof object formula steps           : 21
% 0.15/0.39  # Proof object conjectures             : 16
% 0.15/0.39  # Proof object clause conjectures      : 13
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 16
% 0.15/0.39  # Proof object initial formulas used   : 10
% 0.15/0.39  # Proof object generating inferences   : 14
% 0.15/0.39  # Proof object simplifying inferences  : 6
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 10
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 17
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 17
% 0.15/0.39  # Processed clauses                    : 80
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 4
% 0.15/0.39  # ...remaining for further processing  : 76
% 0.15/0.39  # Other redundant clauses eliminated   : 0
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 6
% 0.15/0.39  # Backward-rewritten                   : 4
% 0.15/0.39  # Generated clauses                    : 162
% 0.15/0.39  # ...of the previous two non-trivial   : 148
% 0.15/0.39  # Contextual simplify-reflections      : 2
% 0.15/0.39  # Paramodulations                      : 162
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 0
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 66
% 0.15/0.39  #    Positive orientable unit clauses  : 8
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 2
% 0.15/0.39  #    Non-unit-clauses                  : 56
% 0.15/0.39  # Current number of unprocessed clauses: 85
% 0.15/0.39  # ...number of literals in the above   : 311
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 10
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 278
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 193
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 11
% 0.15/0.39  # Unit Clause-clause subsumption calls : 49
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 6
% 0.15/0.39  # BW rewrite match successes           : 1
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 3550
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.033 s
% 0.15/0.39  # System time              : 0.003 s
% 0.15/0.39  # Total time               : 0.036 s
% 0.15/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
