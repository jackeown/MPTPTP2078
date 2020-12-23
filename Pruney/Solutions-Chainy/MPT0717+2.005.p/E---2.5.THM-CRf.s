%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  48 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :  162 ( 264 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t172_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t85_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( X2 = k8_relat_1(X1,X3)
          <=> ( ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(X4,k1_relat_1(X3))
                    & r2_hidden(k1_funct_1(X3,X4),X1) ) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v5_relat_1(X2,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( r2_hidden(X3,k1_relat_1(X2))
           => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t172_funct_1])).

fof(c_0_6,plain,(
    ! [X5,X6] :
      ( ( ~ v5_relat_1(X6,X5)
        | r1_tarski(k2_relat_1(X6),X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r1_tarski(k2_relat_1(X6),X5)
        | v5_relat_1(X6,X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v5_relat_1(esk4_0,esk3_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk5_0,k1_relat_1(esk4_0))
    & ~ r2_hidden(k1_funct_1(esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X14,k1_relat_1(X13))
        | ~ r2_hidden(X14,k1_relat_1(X12))
        | X12 != k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(k1_funct_1(X13,X14),X11)
        | ~ r2_hidden(X14,k1_relat_1(X12))
        | X12 != k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X15,k1_relat_1(X13))
        | ~ r2_hidden(k1_funct_1(X13,X15),X11)
        | r2_hidden(X15,k1_relat_1(X12))
        | X12 != k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X16,k1_relat_1(X12))
        | k1_funct_1(X12,X16) = k1_funct_1(X13,X16)
        | X12 != k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X12))
        | ~ r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))
        | ~ r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))
        | ~ r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)
        | X12 = k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_funct_1(X12,esk2_3(X11,X12,X13)) != k1_funct_1(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))
        | ~ r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))
        | ~ r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)
        | X12 = k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X12))
        | r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))
        | r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))
        | X12 = k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_funct_1(X12,esk2_3(X11,X12,X13)) != k1_funct_1(X13,esk2_3(X11,X12,X13))
        | r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))
        | r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))
        | X12 = k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X12))
        | r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)
        | r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))
        | X12 = k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_funct_1(X12,esk2_3(X11,X12,X13)) != k1_funct_1(X13,esk2_3(X11,X12,X13))
        | r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)
        | r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))
        | X12 = k8_relat_1(X11,X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ( v1_relat_1(k8_relat_1(X9,X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k8_relat_1(X9,X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(k2_relat_1(X8),X7)
      | k8_relat_1(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v5_relat_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(X4))
    | X4 != k8_relat_1(X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k8_relat_1(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_13])])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_13])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:45:15 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.37  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.028 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t172_funct_1, conjecture, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.20/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.37  fof(t85_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(X2=k8_relat_1(X1,X3)<=>(![X4]:(r2_hidden(X4,k1_relat_1(X2))<=>(r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X4),X1)))&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 0.20/0.37  fof(fc9_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v1_relat_1(k8_relat_1(X1,X2))&v1_funct_1(k8_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_funct_1)).
% 0.20/0.37  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 0.20/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1)))), inference(assume_negation,[status(cth)],[t172_funct_1])).
% 0.20/0.37  fof(c_0_6, plain, ![X5, X6]:((~v5_relat_1(X6,X5)|r1_tarski(k2_relat_1(X6),X5)|~v1_relat_1(X6))&(~r1_tarski(k2_relat_1(X6),X5)|v5_relat_1(X6,X5)|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.37  fof(c_0_7, negated_conjecture, (((v1_relat_1(esk4_0)&v5_relat_1(esk4_0,esk3_0))&v1_funct_1(esk4_0))&(r2_hidden(esk5_0,k1_relat_1(esk4_0))&~r2_hidden(k1_funct_1(esk4_0,esk5_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.37  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16]:(((((r2_hidden(X14,k1_relat_1(X13))|~r2_hidden(X14,k1_relat_1(X12))|X12!=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(r2_hidden(k1_funct_1(X13,X14),X11)|~r2_hidden(X14,k1_relat_1(X12))|X12!=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X15,k1_relat_1(X13))|~r2_hidden(k1_funct_1(X13,X15),X11)|r2_hidden(X15,k1_relat_1(X12))|X12!=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X16,k1_relat_1(X12))|k1_funct_1(X12,X16)=k1_funct_1(X13,X16)|X12!=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(((r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X12))|(~r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))|(~r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))|~r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)))|X12=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_funct_1(X12,esk2_3(X11,X12,X13))!=k1_funct_1(X13,esk2_3(X11,X12,X13))|(~r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12))|(~r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))|~r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)))|X12=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(((r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X12))|(r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))|r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12)))|X12=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_funct_1(X12,esk2_3(X11,X12,X13))!=k1_funct_1(X13,esk2_3(X11,X12,X13))|(r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X13))|r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12)))|X12=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X12))|(r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)|r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12)))|X12=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_funct_1(X12,esk2_3(X11,X12,X13))!=k1_funct_1(X13,esk2_3(X11,X12,X13))|(r2_hidden(k1_funct_1(X13,esk1_3(X11,X12,X13)),X11)|r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X12)))|X12=k8_relat_1(X11,X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).
% 0.20/0.37  fof(c_0_9, plain, ![X9, X10]:((v1_relat_1(k8_relat_1(X9,X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k8_relat_1(X9,X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).
% 0.20/0.37  fof(c_0_10, plain, ![X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(k2_relat_1(X8),X7)|k8_relat_1(X7,X8)=X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.20/0.37  cnf(c_0_11, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (v5_relat_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_14, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(X4))|X4!=k8_relat_1(X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_15, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_16, plain, (v1_funct_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_17, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.20/0.37  cnf(c_0_19, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_15]), c_0_16])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (k8_relat_1(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_13])])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (~r2_hidden(k1_funct_1(esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),esk3_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_13])])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 26
% 0.20/0.37  # Proof object clause steps            : 15
% 0.20/0.37  # Proof object formula steps           : 11
% 0.20/0.37  # Proof object conjectures             : 12
% 0.20/0.37  # Proof object clause conjectures      : 9
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 10
% 0.20/0.37  # Proof object initial formulas used   : 5
% 0.20/0.37  # Proof object generating inferences   : 4
% 0.20/0.37  # Proof object simplifying inferences  : 12
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 5
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 20
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 20
% 0.20/0.37  # Processed clauses                    : 40
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 40
% 0.20/0.37  # Other redundant clauses eliminated   : 4
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 14
% 0.20/0.37  # ...of the previous two non-trivial   : 9
% 0.20/0.37  # Contextual simplify-reflections      : 8
% 0.20/0.37  # Paramodulations                      : 10
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 4
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 16
% 0.20/0.37  #    Positive orientable unit clauses  : 7
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 8
% 0.20/0.37  # Current number of unprocessed clauses: 9
% 0.20/0.37  # ...number of literals in the above   : 63
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 20
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 443
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 37
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 8
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 2108
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.026 s
% 0.20/0.37  # System time              : 0.007 s
% 0.20/0.37  # Total time               : 0.033 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
