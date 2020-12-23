%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:28 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 201 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_xboole_0(X1,X2)
          & v2_funct_1(X3) )
       => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t121_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_xboole_0(X1,X2)
            & v2_funct_1(X3) )
         => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t125_funct_1])).

fof(c_0_7,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & v2_funct_1(esk5_0)
    & ~ r1_xboole_0(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r1_xboole_0(X12,X13)
        | r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X17,k3_xboole_0(X15,X16))
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_14,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ v2_funct_1(X22)
      | k9_relat_1(X22,k3_xboole_0(X20,X21)) = k3_xboole_0(k9_relat_1(X22,X20),k9_relat_1(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ( k9_relat_1(X19,X18) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X19),X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_xboole_0(k1_relat_1(X19),X18)
        | k9_relat_1(X19,X18) = k1_xboole_0
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_11])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | k9_relat_1(X1,k3_xboole_0(X2,X3)) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(k9_relat_1(X1,esk3_0),k9_relat_1(X1,esk4_0))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_13]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:51:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.40  # and selection function SelectNewComplexAHP.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.037 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t125_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 0.13/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.40  fof(t121_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 0.13/0.40  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.13/0.40  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t125_funct_1])).
% 0.13/0.40  fof(c_0_7, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.40  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((r1_xboole_0(esk3_0,esk4_0)&v2_funct_1(esk5_0))&~r1_xboole_0(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.40  fof(c_0_9, plain, ![X12, X13, X15, X16, X17]:((r1_xboole_0(X12,X13)|r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)))&(~r2_hidden(X17,k3_xboole_0(X15,X16))|~r1_xboole_0(X15,X16))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_10, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_11, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_12, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_13, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.40  fof(c_0_14, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X20, X21, X22]:(~v1_relat_1(X22)|~v1_funct_1(X22)|(~v2_funct_1(X22)|k9_relat_1(X22,k3_xboole_0(X20,X21))=k3_xboole_0(k9_relat_1(X22,X20),k9_relat_1(X22,X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).
% 0.13/0.40  fof(c_0_16, plain, ![X18, X19]:((k9_relat_1(X19,X18)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X19),X18)|~v1_relat_1(X19))&(~r1_xboole_0(k1_relat_1(X19),X18)|k9_relat_1(X19,X18)=k1_xboole_0|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.13/0.40  cnf(c_0_17, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_11])])).
% 0.13/0.40  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_20, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_21, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.40  cnf(c_0_23, plain, (r1_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|k9_relat_1(X1,k3_xboole_0(X2,X3))!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (~r1_xboole_0(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (r1_xboole_0(k9_relat_1(X1,esk3_0),k9_relat_1(X1,esk4_0))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_13]), c_0_24])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 31
% 0.13/0.40  # Proof object clause steps            : 18
% 0.13/0.40  # Proof object formula steps           : 13
% 0.13/0.40  # Proof object conjectures             : 14
% 0.13/0.40  # Proof object clause conjectures      : 11
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 11
% 0.13/0.40  # Proof object initial formulas used   : 6
% 0.13/0.40  # Proof object generating inferences   : 7
% 0.13/0.40  # Proof object simplifying inferences  : 7
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 6
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 15
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 15
% 0.13/0.40  # Processed clauses                    : 94
% 0.13/0.40  # ...of these trivial                  : 8
% 0.13/0.40  # ...subsumed                          : 21
% 0.13/0.40  # ...remaining for further processing  : 65
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 6
% 0.13/0.40  # Backward-rewritten                   : 0
% 0.13/0.40  # Generated clauses                    : 204
% 0.13/0.40  # ...of the previous two non-trivial   : 161
% 0.13/0.40  # Contextual simplify-reflections      : 4
% 0.13/0.40  # Paramodulations                      : 204
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
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
% 0.13/0.40  # Current number of processed clauses  : 59
% 0.13/0.40  #    Positive orientable unit clauses  : 12
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 45
% 0.13/0.40  # Current number of unprocessed clauses: 71
% 0.13/0.40  # ...number of literals in the above   : 457
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 6
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 832
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 88
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 19
% 0.13/0.40  # Unit Clause-clause subsumption calls : 16
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 0
% 0.13/0.40  # BW rewrite match successes           : 0
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 5171
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.043 s
% 0.13/0.40  # System time              : 0.009 s
% 0.13/0.40  # Total time               : 0.053 s
% 0.13/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
