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
% DateTime   : Thu Dec  3 10:55:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  79 expanded)
%              Number of clauses        :   27 (  34 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 352 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t163_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(X1,k1_relat_1(X3))
            & r1_tarski(k9_relat_1(X3,X1),X2) )
         => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t163_funct_1])).

fof(c_0_5,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_tarski(X19,k1_relat_1(X20))
      | r1_tarski(X19,k10_relat_1(X20,k9_relat_1(X20,X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r1_tarski(esk3_0,k1_relat_1(esk5_0))
    & r1_tarski(k9_relat_1(esk5_0,esk3_0),esk4_0)
    & ~ r1_tarski(esk3_0,k10_relat_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X14,k1_relat_1(X11))
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(k1_funct_1(X11,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X15,k1_relat_1(X11))
        | ~ r2_hidden(k1_funct_1(X11,X15),X12)
        | r2_hidden(X15,X13)
        | X13 != k10_relat_1(X11,X12)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk2_3(X11,X16,X17),X17)
        | ~ r2_hidden(esk2_3(X11,X16,X17),k1_relat_1(X11))
        | ~ r2_hidden(k1_funct_1(X11,esk2_3(X11,X16,X17)),X16)
        | X17 = k10_relat_1(X11,X16)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk2_3(X11,X16,X17),k1_relat_1(X11))
        | r2_hidden(esk2_3(X11,X16,X17),X17)
        | X17 = k10_relat_1(X11,X16)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(k1_funct_1(X11,esk2_3(X11,X16,X17)),X16)
        | r2_hidden(esk2_3(X11,X16,X17),X17)
        | X17 = k10_relat_1(X11,X16)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)))
    | ~ r1_tarski(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk3_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_8])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk3_0)))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk5_0,X2))
    | ~ r2_hidden(k1_funct_1(esk5_0,X1),X2)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_8])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(esk5_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk1_2(esk3_0,X1)),k9_relat_1(esk5_0,esk3_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k10_relat_1(esk5_0,X2))
    | r1_tarski(esk3_0,X1)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk1_2(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk1_2(esk3_0,X1)),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k10_relat_1(esk5_0,esk4_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k10_relat_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.19/0.37  # and selection function SelectCQIAr.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t163_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.19/0.37  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.19/0.37  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t163_funct_1])).
% 0.19/0.37  fof(c_0_5, plain, ![X19, X20]:(~v1_relat_1(X20)|(~r1_tarski(X19,k1_relat_1(X20))|r1_tarski(X19,k10_relat_1(X20,k9_relat_1(X20,X19))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((r1_tarski(esk3_0,k1_relat_1(esk5_0))&r1_tarski(k9_relat_1(esk5_0,esk3_0),esk4_0))&~r1_tarski(esk3_0,k10_relat_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.37  cnf(c_0_7, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_8, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  fof(c_0_9, plain, ![X11, X12, X13, X14, X15, X16, X17]:((((r2_hidden(X14,k1_relat_1(X11))|~r2_hidden(X14,X13)|X13!=k10_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(r2_hidden(k1_funct_1(X11,X14),X12)|~r2_hidden(X14,X13)|X13!=k10_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(X15,k1_relat_1(X11))|~r2_hidden(k1_funct_1(X11,X15),X12)|r2_hidden(X15,X13)|X13!=k10_relat_1(X11,X12)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((~r2_hidden(esk2_3(X11,X16,X17),X17)|(~r2_hidden(esk2_3(X11,X16,X17),k1_relat_1(X11))|~r2_hidden(k1_funct_1(X11,esk2_3(X11,X16,X17)),X16))|X17=k10_relat_1(X11,X16)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&((r2_hidden(esk2_3(X11,X16,X17),k1_relat_1(X11))|r2_hidden(esk2_3(X11,X16,X17),X17)|X17=k10_relat_1(X11,X16)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(r2_hidden(k1_funct_1(X11,esk2_3(X11,X16,X17)),X16)|r2_hidden(esk2_3(X11,X16,X17),X17)|X17=k10_relat_1(X11,X16)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.19/0.37  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk5_0,k9_relat_1(esk5_0,X1)))|~r1_tarski(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_13, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,X4)|X4!=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (r1_tarski(esk3_0,k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_16, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_17, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))), inference(er,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk3_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_21, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(k1_funct_1(X2,X1),X3)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk5_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_12])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),X2)|~r2_hidden(X1,k10_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_8])])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k10_relat_1(esk5_0,k9_relat_1(esk5_0,esk3_0)))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk5_0,X2))|~r2_hidden(k1_funct_1(esk5_0,X1),X2)|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_8])])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(esk5_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k9_relat_1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_23])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk1_2(esk3_0,X1)),k9_relat_1(esk5_0,esk3_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k10_relat_1(esk5_0,X2))|r1_tarski(esk3_0,X1)|~r2_hidden(k1_funct_1(esk5_0,esk1_2(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk1_2(esk3_0,X1)),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.37  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k10_relat_1(esk5_0,esk4_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (~r1_tarski(esk3_0,k10_relat_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 36
% 0.19/0.37  # Proof object clause steps            : 27
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 22
% 0.19/0.37  # Proof object clause conjectures      : 19
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 11
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 14
% 0.19/0.37  # Proof object simplifying inferences  : 7
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 15
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 15
% 0.19/0.37  # Processed clauses                    : 64
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 5
% 0.19/0.37  # ...remaining for further processing  : 59
% 0.19/0.37  # Other redundant clauses eliminated   : 3
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 69
% 0.19/0.37  # ...of the previous two non-trivial   : 61
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 64
% 0.19/0.37  # Factorizations                       : 2
% 0.19/0.37  # Equation resolutions                 : 3
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
% 0.19/0.37  #    Positive orientable unit clauses  : 8
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 32
% 0.19/0.37  # Current number of unprocessed clauses: 25
% 0.19/0.37  # ...number of literals in the above   : 70
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 15
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 96
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 77
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.19/0.37  # Unit Clause-clause subsumption calls : 6
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 10
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2556
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.032 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
