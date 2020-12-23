%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:35 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 215 expanded)
%              Number of clauses        :   37 (  88 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 (1209 expanded)
%              Number of equality atoms :   26 ( 174 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(fc2_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ v1_xboole_0(k1_ordinal1(X1))
        & v3_ordinal1(k1_ordinal1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(t42_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ ( ~ v4_ordinal1(X1)
            & ! [X2] :
                ( v3_ordinal1(X2)
               => X1 != k1_ordinal1(X2) ) )
        & ~ ( ? [X2] :
                ( v3_ordinal1(X2)
                & X1 = k1_ordinal1(X2) )
            & v4_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(X11,X12)
        | r1_ordinal1(k1_ordinal1(X11),X12)
        | ~ v3_ordinal1(X12)
        | ~ v3_ordinal1(X11) )
      & ( ~ r1_ordinal1(k1_ordinal1(X11),X12)
        | r2_hidden(X11,X12)
        | ~ v3_ordinal1(X12)
        | ~ v3_ordinal1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ( ~ v4_ordinal1(X15)
        | ~ v3_ordinal1(X16)
        | ~ r2_hidden(X16,X15)
        | r2_hidden(k1_ordinal1(X16),X15)
        | ~ v3_ordinal1(X15) )
      & ( v3_ordinal1(esk1_1(X15))
        | v4_ordinal1(X15)
        | ~ v3_ordinal1(X15) )
      & ( r2_hidden(esk1_1(X15),X15)
        | v4_ordinal1(X15)
        | ~ v3_ordinal1(X15) )
      & ( ~ r2_hidden(k1_ordinal1(esk1_1(X15)),X15)
        | v4_ordinal1(X15)
        | ~ v3_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

fof(c_0_11,plain,(
    ! [X13,X14] :
      ( ( ~ r2_hidden(X13,k1_ordinal1(X14))
        | r1_ordinal1(X13,X14)
        | ~ v3_ordinal1(X14)
        | ~ v3_ordinal1(X13) )
      & ( ~ r1_ordinal1(X13,X14)
        | r2_hidden(X13,k1_ordinal1(X14))
        | ~ v3_ordinal1(X14)
        | ~ v3_ordinal1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

cnf(c_0_12,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v3_ordinal1(esk1_1(X1))
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v4_ordinal1(X1)
    | r1_ordinal1(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_17,plain,(
    ! [X5] :
      ( ( ~ v1_xboole_0(k1_ordinal1(X5))
        | ~ v3_ordinal1(X5) )
      & ( v3_ordinal1(k1_ordinal1(X5))
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( ~ ( ~ v4_ordinal1(X1)
              & ! [X2] :
                  ( v3_ordinal1(X2)
                 => X1 != k1_ordinal1(X2) ) )
          & ~ ( ? [X2] :
                  ( v3_ordinal1(X2)
                  & X1 = k1_ordinal1(X2) )
              & v4_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_ordinal1])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ( ~ r2_hidden(X8,k1_ordinal1(X9))
        | r2_hidden(X8,X9)
        | X8 = X9 )
      & ( ~ r2_hidden(X8,X9)
        | r2_hidden(X8,k1_ordinal1(X9)) )
      & ( X8 != X9
        | r2_hidden(X8,k1_ordinal1(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_20,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(k1_ordinal1(esk1_1(X1)),k1_ordinal1(X1))
    | ~ v3_ordinal1(k1_ordinal1(esk1_1(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,(
    ! [X19] :
      ( v3_ordinal1(esk2_0)
      & ( v3_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v4_ordinal1(esk2_0)
        | ~ v4_ordinal1(esk2_0) )
      & ( v3_ordinal1(esk3_0)
        | ~ v3_ordinal1(X19)
        | esk2_0 != k1_ordinal1(X19) )
      & ( esk2_0 = k1_ordinal1(esk3_0)
        | ~ v3_ordinal1(X19)
        | esk2_0 != k1_ordinal1(X19) )
      & ( v4_ordinal1(esk2_0)
        | ~ v3_ordinal1(X19)
        | esk2_0 != k1_ordinal1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v4_ordinal1(X1)
    | r2_hidden(k1_ordinal1(esk1_1(X1)),k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])).

cnf(c_0_25,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk1_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | ~ v3_ordinal1(X1)
    | esk2_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_ordinal1(esk1_1(X1)) = X1
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v4_ordinal1(esk2_0)
    | ~ v3_ordinal1(esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])]),c_0_28])])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 = k1_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v4_ordinal1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    | ~ v4_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_ordinal1(X1),k1_ordinal1(X1))
    | ~ v4_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k1_ordinal1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34])])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ( ~ r1_ordinal1(X6,X7)
        | r1_tarski(X6,X7)
        | ~ v3_ordinal1(X6)
        | ~ v3_ordinal1(X7) )
      & ( ~ r1_tarski(X6,X7)
        | r1_ordinal1(X6,X7)
        | ~ v3_ordinal1(X6)
        | ~ v3_ordinal1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_41,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_ordinal1(k1_ordinal1(X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34]),c_0_39])])).

fof(c_0_44,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_ordinal1(X1,k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_21])).

fof(c_0_47,plain,(
    ! [X10] : X10 != k1_ordinal1(X10) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

cnf(c_0_48,negated_conjecture,
    ( r1_ordinal1(k1_ordinal1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_43]),c_0_28])])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_21])).

cnf(c_0_51,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_ordinal1(esk2_0),esk2_0)
    | ~ v3_ordinal1(k1_ordinal1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_48]),c_0_28])])).

cnf(c_0_53,plain,
    ( ~ v3_ordinal1(X1)
    | ~ r1_tarski(k1_ordinal1(X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_ordinal1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_21]),c_0_28])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.21/0.38  # and selection function SelectNewComplexAHPNS.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.028 s
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.21/0.38  fof(t41_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.21/0.38  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.21/0.38  fof(fc2_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(~(v1_xboole_0(k1_ordinal1(X1)))&v3_ordinal1(k1_ordinal1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_ordinal1)).
% 0.21/0.38  fof(t42_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_ordinal1)).
% 0.21/0.38  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.21/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.21/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.38  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.21/0.38  fof(c_0_9, plain, ![X11, X12]:((~r2_hidden(X11,X12)|r1_ordinal1(k1_ordinal1(X11),X12)|~v3_ordinal1(X12)|~v3_ordinal1(X11))&(~r1_ordinal1(k1_ordinal1(X11),X12)|r2_hidden(X11,X12)|~v3_ordinal1(X12)|~v3_ordinal1(X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 0.21/0.38  fof(c_0_10, plain, ![X15, X16]:((~v4_ordinal1(X15)|(~v3_ordinal1(X16)|(~r2_hidden(X16,X15)|r2_hidden(k1_ordinal1(X16),X15)))|~v3_ordinal1(X15))&((v3_ordinal1(esk1_1(X15))|v4_ordinal1(X15)|~v3_ordinal1(X15))&((r2_hidden(esk1_1(X15),X15)|v4_ordinal1(X15)|~v3_ordinal1(X15))&(~r2_hidden(k1_ordinal1(esk1_1(X15)),X15)|v4_ordinal1(X15)|~v3_ordinal1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).
% 0.21/0.38  fof(c_0_11, plain, ![X13, X14]:((~r2_hidden(X13,k1_ordinal1(X14))|r1_ordinal1(X13,X14)|~v3_ordinal1(X14)|~v3_ordinal1(X13))&(~r1_ordinal1(X13,X14)|r2_hidden(X13,k1_ordinal1(X14))|~v3_ordinal1(X14)|~v3_ordinal1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 0.21/0.38  cnf(c_0_12, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_13, plain, (r2_hidden(esk1_1(X1),X1)|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_14, plain, (v3_ordinal1(esk1_1(X1))|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_15, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_16, plain, (v4_ordinal1(X1)|r1_ordinal1(k1_ordinal1(esk1_1(X1)),X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.21/0.38  fof(c_0_17, plain, ![X5]:((~v1_xboole_0(k1_ordinal1(X5))|~v3_ordinal1(X5))&(v3_ordinal1(k1_ordinal1(X5))|~v3_ordinal1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_ordinal1])])])])).
% 0.21/0.38  fof(c_0_18, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1)))))), inference(assume_negation,[status(cth)],[t42_ordinal1])).
% 0.21/0.38  fof(c_0_19, plain, ![X8, X9]:((~r2_hidden(X8,k1_ordinal1(X9))|(r2_hidden(X8,X9)|X8=X9))&((~r2_hidden(X8,X9)|r2_hidden(X8,k1_ordinal1(X9)))&(X8!=X9|r2_hidden(X8,k1_ordinal1(X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.21/0.38  cnf(c_0_20, plain, (v4_ordinal1(X1)|r2_hidden(k1_ordinal1(esk1_1(X1)),k1_ordinal1(X1))|~v3_ordinal1(k1_ordinal1(esk1_1(X1)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.38  cnf(c_0_21, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  fof(c_0_22, negated_conjecture, ![X19]:(v3_ordinal1(esk2_0)&((((v3_ordinal1(esk3_0)|~v4_ordinal1(esk2_0))&(esk2_0=k1_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)))&(v4_ordinal1(esk2_0)|~v4_ordinal1(esk2_0)))&(((v3_ordinal1(esk3_0)|(~v3_ordinal1(X19)|esk2_0!=k1_ordinal1(X19)))&(esk2_0=k1_ordinal1(esk3_0)|(~v3_ordinal1(X19)|esk2_0!=k1_ordinal1(X19))))&(v4_ordinal1(esk2_0)|(~v3_ordinal1(X19)|esk2_0!=k1_ordinal1(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])])).
% 0.21/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_24, plain, (v4_ordinal1(X1)|r2_hidden(k1_ordinal1(esk1_1(X1)),k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_14])).
% 0.21/0.38  cnf(c_0_25, plain, (v4_ordinal1(X1)|~r2_hidden(k1_ordinal1(esk1_1(X1)),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (v4_ordinal1(esk2_0)|~v3_ordinal1(X1)|esk2_0!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_27, plain, (k1_ordinal1(esk1_1(X1))=X1|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_29, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (v4_ordinal1(esk2_0)|~v3_ordinal1(esk1_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])]), c_0_28])])).
% 0.21/0.38  cnf(c_0_31, plain, (r2_hidden(k1_ordinal1(X2),X1)|~v4_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_32, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (esk2_0=k1_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (v4_ordinal1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_28])])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (v3_ordinal1(esk3_0)|~v4_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_36, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_37, plain, (r2_hidden(k1_ordinal1(X1),k1_ordinal1(X1))|~v4_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_21])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (k1_ordinal1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (v3_ordinal1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_34])])).
% 0.21/0.38  fof(c_0_40, plain, ![X6, X7]:((~r1_ordinal1(X6,X7)|r1_tarski(X6,X7)|(~v3_ordinal1(X6)|~v3_ordinal1(X7)))&(~r1_tarski(X6,X7)|r1_ordinal1(X6,X7)|(~v3_ordinal1(X6)|~v3_ordinal1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.21/0.38  cnf(c_0_41, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_42, plain, (r2_hidden(X1,k1_ordinal1(k1_ordinal1(X1)))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_34]), c_0_39])])).
% 0.21/0.39  fof(c_0_44, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.39  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.39  cnf(c_0_46, plain, (r1_ordinal1(X1,k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_21])).
% 0.21/0.39  fof(c_0_47, plain, ![X10]:X10!=k1_ordinal1(X10), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (r1_ordinal1(k1_ordinal1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_43]), c_0_28])])).
% 0.21/0.39  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.39  cnf(c_0_50, plain, (r1_tarski(X1,k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_21])).
% 0.21/0.39  cnf(c_0_51, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_ordinal1(esk2_0),esk2_0)|~v3_ordinal1(k1_ordinal1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_48]), c_0_28])])).
% 0.21/0.39  cnf(c_0_53, plain, (~v3_ordinal1(X1)|~r1_tarski(k1_ordinal1(X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_ordinal1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_21]), c_0_28])])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_28])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 56
% 0.21/0.39  # Proof object clause steps            : 37
% 0.21/0.39  # Proof object formula steps           : 19
% 0.21/0.39  # Proof object conjectures             : 16
% 0.21/0.39  # Proof object clause conjectures      : 13
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 18
% 0.21/0.39  # Proof object initial formulas used   : 9
% 0.21/0.39  # Proof object generating inferences   : 16
% 0.21/0.39  # Proof object simplifying inferences  : 28
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 9
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 26
% 0.21/0.39  # Removed in clause preprocessing      : 1
% 0.21/0.39  # Initial clauses in saturation        : 25
% 0.21/0.39  # Processed clauses                    : 140
% 0.21/0.39  # ...of these trivial                  : 8
% 0.21/0.39  # ...subsumed                          : 16
% 0.21/0.39  # ...remaining for further processing  : 116
% 0.21/0.39  # Other redundant clauses eliminated   : 6
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 10
% 0.21/0.39  # Backward-rewritten                   : 9
% 0.21/0.39  # Generated clauses                    : 344
% 0.21/0.39  # ...of the previous two non-trivial   : 275
% 0.21/0.39  # Contextual simplify-reflections      : 17
% 0.21/0.39  # Paramodulations                      : 338
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 6
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 94
% 0.21/0.39  #    Positive orientable unit clauses  : 35
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 4
% 0.21/0.39  #    Non-unit-clauses                  : 55
% 0.21/0.39  # Current number of unprocessed clauses: 158
% 0.21/0.39  # ...number of literals in the above   : 565
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 19
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 647
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 468
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 42
% 0.21/0.39  # Unit Clause-clause subsumption calls : 1
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 72
% 0.21/0.39  # BW rewrite match successes           : 6
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 7287
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.033 s
% 0.21/0.39  # System time              : 0.006 s
% 0.21/0.39  # Total time               : 0.040 s
% 0.21/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
