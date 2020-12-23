%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 101 expanded)
%              Number of clauses        :   26 (  37 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 368 expanded)
%              Number of equality atoms :   24 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t177_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v2_funct_1(X1)
            & r1_tarski(X2,k1_relat_1(X1)) )
         => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t157_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v2_funct_1(X1)
              & r1_tarski(X2,k1_relat_1(X1)) )
           => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t177_funct_1])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & r1_tarski(esk2_0,k1_relat_1(esk1_0))
    & k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k9_relat_1(X6,k1_relat_1(X6)) = k2_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r1_tarski(k9_relat_1(X18,X16),k9_relat_1(X18,X17))
      | ~ r1_tarski(X16,k1_relat_1(X18))
      | ~ v2_funct_1(X18)
      | r1_tarski(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ r1_tarski(X10,k2_relat_1(X11))
      | k9_relat_1(X11,k10_relat_1(X11,X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( k9_relat_1(esk1_0,k1_relat_1(esk1_0)) = k2_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_24,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ v2_funct_1(X15)
      | k10_relat_1(X15,X14) = k9_relat_1(k2_funct_1(X15),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))
    | ~ r1_tarski(X1,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_15])])).

cnf(c_0_27,negated_conjecture,
    ( k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1)) = X1
    | ~ r1_tarski(X1,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_15])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk2_0),k2_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v2_funct_1(X13)
      | r1_tarski(k10_relat_1(X13,k9_relat_1(X13,X12)),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

cnf(c_0_31,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k9_relat_1(esk1_0,esk2_0),k9_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k9_relat_1(esk1_0,k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0))) = k9_relat_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk1_0),X1) = k10_relat_1(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_19]),c_0_15])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_0,k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,k9_relat_1(esk1_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_18]),c_0_19]),c_0_15])])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.19/0.37  # and selection function PSelectSmallestOrientable.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t177_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 0.19/0.37  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.19/0.37  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.37  fof(t157_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 0.19/0.37  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.19/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.37  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 0.19/0.37  fof(t152_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2))), inference(assume_negation,[status(cth)],[t177_funct_1])).
% 0.19/0.37  fof(c_0_9, plain, ![X7, X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(X7,X8)|r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v2_funct_1(esk1_0)&r1_tarski(esk2_0,k1_relat_1(esk1_0)))&k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0))!=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X6]:(~v1_relat_1(X6)|k9_relat_1(X6,k1_relat_1(X6))=k2_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.37  fof(c_0_12, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r1_tarski(k9_relat_1(X18,X16),k9_relat_1(X18,X17))|~r1_tarski(X16,k1_relat_1(X18))|~v2_funct_1(X18)|r1_tarski(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).
% 0.19/0.37  fof(c_0_13, plain, ![X10, X11]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~r1_tarski(X10,k2_relat_1(X11))|k9_relat_1(X11,k10_relat_1(X11,X10))=X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.19/0.37  cnf(c_0_14, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_16, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_17, plain, (r1_tarski(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_20, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k9_relat_1(esk1_0,k1_relat_1(esk1_0))=k2_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.19/0.37  fof(c_0_24, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.37  fof(c_0_25, plain, ![X14, X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|(~v2_funct_1(X15)|k10_relat_1(X15,X14)=k9_relat_1(k2_funct_1(X15),X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))|~r1_tarski(X1,k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_15])])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1))=X1|~r1_tarski(X1,k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_19]), c_0_15])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk2_0),k2_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.19/0.37  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  fof(c_0_30, plain, ![X12, X13]:(~v1_relat_1(X13)|~v1_funct_1(X13)|(~v2_funct_1(X13)|r1_tarski(k10_relat_1(X13,k9_relat_1(X13,X12)),X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).
% 0.19/0.37  cnf(c_0_31, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k9_relat_1(esk1_0,esk2_0),k9_relat_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_22])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (k9_relat_1(esk1_0,k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0)))=k9_relat_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_35, plain, (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (k9_relat_1(k2_funct_1(esk1_0),k9_relat_1(esk1_0,esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (k9_relat_1(k2_funct_1(esk1_0),X1)=k10_relat_1(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_19]), c_0_15])])).
% 0.19/0.37  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_0,k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,k9_relat_1(esk1_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_18]), c_0_19]), c_0_15])])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk1_0,k9_relat_1(esk1_0,esk2_0))!=esk2_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])]), c_0_41]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 43
% 0.19/0.37  # Proof object clause steps            : 26
% 0.19/0.37  # Proof object formula steps           : 17
% 0.19/0.37  # Proof object conjectures             : 20
% 0.19/0.37  # Proof object clause conjectures      : 17
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 8
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 19
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 8
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 14
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 14
% 0.19/0.37  # Processed clauses                    : 52
% 0.19/0.37  # ...of these trivial                  : 2
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 48
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 69
% 0.19/0.37  # ...of the previous two non-trivial   : 53
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 67
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
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
% 0.19/0.37  # Current number of processed clauses  : 31
% 0.19/0.37  #    Positive orientable unit clauses  : 14
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 16
% 0.19/0.37  # Current number of unprocessed clauses: 28
% 0.19/0.37  # ...number of literals in the above   : 54
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 15
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 19
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 3
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 11
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2290
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.028 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.033 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
