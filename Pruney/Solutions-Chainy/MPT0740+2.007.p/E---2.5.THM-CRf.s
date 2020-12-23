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
% DateTime   : Thu Dec  3 10:56:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  70 expanded)
%              Number of clauses        :   26 (  32 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 208 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

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

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t30_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(c_0_10,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k3_tarski(X9),X10)
      | ~ r2_hidden(X11,X9)
      | r1_tarski(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(k3_tarski(X7),k3_tarski(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_ordinal1(X13)
        | ~ r2_hidden(X14,X13)
        | r1_tarski(X14,X13) )
      & ( r2_hidden(esk2_1(X15),X15)
        | v1_ordinal1(X15) )
      & ( ~ r1_tarski(esk2_1(X15),X15)
        | v1_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_tarski(k3_tarski(X4),X5) )
      & ( ~ r1_tarski(esk1_2(X4,X5),X5)
        | r1_tarski(k3_tarski(X4),X5) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_ordinal1(X18)
      | ~ v3_ordinal1(X19)
      | ~ v3_ordinal1(X20)
      | ~ r1_tarski(X18,X19)
      | ~ r2_hidden(X19,X20)
      | r2_hidden(X18,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ~ v3_ordinal1(X22)
      | ~ r2_hidden(X21,X22)
      | v3_ordinal1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_22,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v1_ordinal1(X1)
    | r1_tarski(esk2_1(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r1_tarski(esk1_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r1_tarski(k3_tarski(X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(X1),X1)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_31])).

fof(c_0_33,plain,(
    ! [X17] : r2_hidden(X17,k1_ordinal1(X17)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t30_ordinal1])).

cnf(c_0_35,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X23] :
      ( ~ v3_ordinal1(X23)
      | v3_ordinal1(k1_ordinal1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_38,plain,(
    ! [X12] :
      ( ( v1_ordinal1(X12)
        | ~ v3_ordinal1(X12) )
      & ( v2_ordinal1(X12)
        | ~ v3_ordinal1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_39,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & ~ v3_ordinal1(k3_tarski(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

cnf(c_0_40,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:33:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.19/0.37  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.19/0.37  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.19/0.37  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.19/0.37  fof(t22_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r1_tarski(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_ordinal1)).
% 0.19/0.37  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.19/0.37  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.19/0.37  fof(t30_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 0.19/0.37  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.19/0.37  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.19/0.37  fof(c_0_10, plain, ![X9, X10, X11]:(~r1_tarski(k3_tarski(X9),X10)|~r2_hidden(X11,X9)|r1_tarski(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.19/0.37  fof(c_0_11, plain, ![X7, X8]:(~r1_tarski(X7,X8)|r1_tarski(k3_tarski(X7),k3_tarski(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.19/0.37  cnf(c_0_12, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_13, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  fof(c_0_14, plain, ![X13, X14, X15]:((~v1_ordinal1(X13)|(~r2_hidden(X14,X13)|r1_tarski(X14,X13)))&((r2_hidden(esk2_1(X15),X15)|v1_ordinal1(X15))&(~r1_tarski(esk2_1(X15),X15)|v1_ordinal1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X4, X5]:((r2_hidden(esk1_2(X4,X5),X4)|r1_tarski(k3_tarski(X4),X5))&(~r1_tarski(esk1_2(X4,X5),X5)|r1_tarski(k3_tarski(X4),X5))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.19/0.37  cnf(c_0_16, plain, (r1_tarski(X1,k3_tarski(X2))|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.37  cnf(c_0_17, plain, (r2_hidden(esk2_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_18, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  fof(c_0_20, plain, ![X18, X19, X20]:(~v1_ordinal1(X18)|(~v3_ordinal1(X19)|(~v3_ordinal1(X20)|(~r1_tarski(X18,X19)|~r2_hidden(X19,X20)|r2_hidden(X18,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).
% 0.19/0.37  fof(c_0_21, plain, ![X21, X22]:(~v3_ordinal1(X22)|(~r2_hidden(X21,X22)|v3_ordinal1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.19/0.37  cnf(c_0_22, plain, (v1_ordinal1(X1)|~r1_tarski(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_23, plain, (v1_ordinal1(X1)|r1_tarski(esk2_1(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.37  cnf(c_0_24, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_25, plain, (r1_tarski(esk1_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.37  cnf(c_0_26, plain, (r2_hidden(X1,X3)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_27, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_28, plain, (v1_ordinal1(k3_tarski(X1))|~r1_tarski(k3_tarski(X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_29, plain, (r1_tarski(k3_tarski(X1),X1)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X3)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_31, plain, (v1_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.37  cnf(c_0_32, plain, (r2_hidden(k3_tarski(X1),X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_31])).
% 0.19/0.37  fof(c_0_33, plain, ![X17]:r2_hidden(X17,k1_ordinal1(X17)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.19/0.37  fof(c_0_34, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t30_ordinal1])).
% 0.19/0.37  cnf(c_0_35, plain, (v3_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_32])).
% 0.19/0.37  cnf(c_0_36, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  fof(c_0_37, plain, ![X23]:(~v3_ordinal1(X23)|v3_ordinal1(k1_ordinal1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.19/0.37  fof(c_0_38, plain, ![X12]:((v1_ordinal1(X12)|~v3_ordinal1(X12))&(v2_ordinal1(X12)|~v3_ordinal1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.19/0.37  fof(c_0_39, negated_conjecture, (v3_ordinal1(esk3_0)&~v3_ordinal1(k3_tarski(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.19/0.37  cnf(c_0_40, plain, (v3_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)|~v3_ordinal1(k1_ordinal1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.37  cnf(c_0_41, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_42, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (~v3_ordinal1(k3_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.37  cnf(c_0_44, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 47
% 0.19/0.37  # Proof object clause steps            : 26
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 6
% 0.19/0.37  # Proof object clause conjectures      : 3
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 14
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 5
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 15
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 15
% 0.19/0.37  # Processed clauses                    : 44
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 3
% 0.19/0.37  # ...remaining for further processing  : 41
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 56
% 0.19/0.37  # ...of the previous two non-trivial   : 53
% 0.19/0.37  # Contextual simplify-reflections      : 3
% 0.19/0.37  # Paramodulations                      : 56
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 41
% 0.19/0.37  #    Positive orientable unit clauses  : 2
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 38
% 0.19/0.37  # Current number of unprocessed clauses: 24
% 0.19/0.37  # ...number of literals in the above   : 97
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 0
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 127
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 93
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1923
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.028 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
