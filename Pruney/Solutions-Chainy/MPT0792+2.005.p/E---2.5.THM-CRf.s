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
% DateTime   : Thu Dec  3 10:56:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 113 expanded)
%              Number of clauses        :   23 (  38 expanded)
%              Number of leaves         :    5 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  190 ( 749 expanded)
%              Number of equality atoms :   17 (  80 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3))
          & ! [X4] :
              ( r2_hidden(X4,k1_wellord1(X3,X1))
             => ( r2_hidden(k4_tarski(X4,X2),X3)
                & X4 != X2 ) ) )
       => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(t38_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
        <=> ( X1 = X2
            | r2_hidden(X1,k1_wellord1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(t37_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3))
            & ! [X4] :
                ( r2_hidden(X4,k1_wellord1(X3,X1))
               => ( r2_hidden(k4_tarski(X4,X2),X3)
                  & X4 != X2 ) ) )
         => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t42_wellord1])).

fof(c_0_6,plain,(
    ! [X5] :
      ( ( v1_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v8_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v4_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v6_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v1_wellord1(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( ~ v1_relat_2(X5)
        | ~ v8_relat_2(X5)
        | ~ v4_relat_2(X5)
        | ~ v6_relat_2(X5)
        | ~ v1_wellord1(X5)
        | v2_wellord1(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_7,negated_conjecture,(
    ! [X20] :
      ( v1_relat_1(esk5_0)
      & v2_wellord1(esk5_0)
      & r2_hidden(esk3_0,k3_relat_1(esk5_0))
      & r2_hidden(esk4_0,k3_relat_1(esk5_0))
      & ( r2_hidden(k4_tarski(X20,esk4_0),esk5_0)
        | ~ r2_hidden(X20,k1_wellord1(esk5_0,esk3_0)) )
      & ( X20 != esk4_0
        | ~ r2_hidden(X20,k1_wellord1(esk5_0,esk3_0)) )
      & ~ r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v6_relat_2(X6)
        | ~ r2_hidden(X7,k3_relat_1(X6))
        | ~ r2_hidden(X8,k3_relat_1(X6))
        | X7 = X8
        | r2_hidden(k4_tarski(X7,X8),X6)
        | r2_hidden(k4_tarski(X8,X7),X6)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_1(X6),k3_relat_1(X6))
        | v6_relat_2(X6)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk2_1(X6),k3_relat_1(X6))
        | v6_relat_2(X6)
        | ~ v1_relat_1(X6) )
      & ( esk1_1(X6) != esk2_1(X6)
        | v6_relat_2(X6)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_1(X6),esk2_1(X6)),X6)
        | v6_relat_2(X6)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X6),esk1_1(X6)),X6)
        | v6_relat_2(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_9,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v2_wellord1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r1_tarski(k1_wellord1(X16,X14),k1_wellord1(X16,X15))
        | X14 = X15
        | r2_hidden(X14,k1_wellord1(X16,X15))
        | ~ v2_wellord1(X16)
        | ~ r2_hidden(X14,k3_relat_1(X16))
        | ~ r2_hidden(X15,k3_relat_1(X16))
        | ~ v1_relat_1(X16) )
      & ( X14 != X15
        | r1_tarski(k1_wellord1(X16,X14),k1_wellord1(X16,X15))
        | ~ v2_wellord1(X16)
        | ~ r2_hidden(X14,k3_relat_1(X16))
        | ~ r2_hidden(X15,k3_relat_1(X16))
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(X14,k1_wellord1(X16,X15))
        | r1_tarski(k1_wellord1(X16,X14),k1_wellord1(X16,X15))
        | ~ v2_wellord1(X16)
        | ~ r2_hidden(X14,k3_relat_1(X16))
        | ~ r2_hidden(X15,k3_relat_1(X16))
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_wellord1])])])).

cnf(c_0_13,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v6_relat_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
    | X1 != X2
    | ~ v2_wellord1(X3)
    | ~ r2_hidden(X1,k3_relat_1(X3))
    | ~ r2_hidden(X2,k3_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_hidden(k4_tarski(X11,X12),X13)
        | r1_tarski(k1_wellord1(X13,X11),k1_wellord1(X13,X12))
        | ~ v2_wellord1(X13)
        | ~ r2_hidden(X11,k3_relat_1(X13))
        | ~ r2_hidden(X12,k3_relat_1(X13))
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k1_wellord1(X13,X11),k1_wellord1(X13,X12))
        | r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v2_wellord1(X13)
        | ~ r2_hidden(X11,k3_relat_1(X13))
        | ~ r2_hidden(X12,k3_relat_1(X13))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_wellord1])])])).

cnf(c_0_18,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(k4_tarski(X1,esk4_0),esk5_0)
    | r2_hidden(k4_tarski(esk4_0,X1),esk5_0)
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X2))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v2_wellord1(X3)
    | ~ r2_hidden(X1,k3_relat_1(X3))
    | ~ r2_hidden(X2,k3_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(k4_tarski(esk4_0,esk3_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( X1 != esk4_0
    | ~ r2_hidden(X1,k1_wellord1(esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk5_0,X1),k1_wellord1(esk5_0,X1))
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_10]),c_0_11])])).

cnf(c_0_27,plain,
    ( X2 = X3
    | r2_hidden(X2,k1_wellord1(X1,X3))
    | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 = esk3_0
    | r1_tarski(k1_wellord1(esk5_0,esk4_0),k1_wellord1(esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19]),c_0_14]),c_0_10]),c_0_11])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_wellord1(esk5_0,esk3_0)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),esk5_0)
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_10]),c_0_11])])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19]),c_0_14]),c_0_10]),c_0_11])]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_31]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t42_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&![X4]:(r2_hidden(X4,k1_wellord1(X3,X1))=>(r2_hidden(k4_tarski(X4,X2),X3)&X4!=X2)))=>r2_hidden(k4_tarski(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_wellord1)).
% 0.20/0.38  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.20/0.38  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 0.20/0.38  fof(t38_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))<=>(X1=X2|r2_hidden(X1,k1_wellord1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_wellord1)).
% 0.20/0.38  fof(t37_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&![X4]:(r2_hidden(X4,k1_wellord1(X3,X1))=>(r2_hidden(k4_tarski(X4,X2),X3)&X4!=X2)))=>r2_hidden(k4_tarski(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t42_wellord1])).
% 0.20/0.38  fof(c_0_6, plain, ![X5]:((((((v1_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5))&(v8_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(v4_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(v6_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(v1_wellord1(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(~v1_relat_2(X5)|~v8_relat_2(X5)|~v4_relat_2(X5)|~v6_relat_2(X5)|~v1_wellord1(X5)|v2_wellord1(X5)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ![X20]:(v1_relat_1(esk5_0)&((((v2_wellord1(esk5_0)&r2_hidden(esk3_0,k3_relat_1(esk5_0)))&r2_hidden(esk4_0,k3_relat_1(esk5_0)))&((r2_hidden(k4_tarski(X20,esk4_0),esk5_0)|~r2_hidden(X20,k1_wellord1(esk5_0,esk3_0)))&(X20!=esk4_0|~r2_hidden(X20,k1_wellord1(esk5_0,esk3_0)))))&~r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X6, X7, X8]:((~v6_relat_2(X6)|(~r2_hidden(X7,k3_relat_1(X6))|~r2_hidden(X8,k3_relat_1(X6))|X7=X8|r2_hidden(k4_tarski(X7,X8),X6)|r2_hidden(k4_tarski(X8,X7),X6))|~v1_relat_1(X6))&(((((r2_hidden(esk1_1(X6),k3_relat_1(X6))|v6_relat_2(X6)|~v1_relat_1(X6))&(r2_hidden(esk2_1(X6),k3_relat_1(X6))|v6_relat_2(X6)|~v1_relat_1(X6)))&(esk1_1(X6)!=esk2_1(X6)|v6_relat_2(X6)|~v1_relat_1(X6)))&(~r2_hidden(k4_tarski(esk1_1(X6),esk2_1(X6)),X6)|v6_relat_2(X6)|~v1_relat_1(X6)))&(~r2_hidden(k4_tarski(esk2_1(X6),esk1_1(X6)),X6)|v6_relat_2(X6)|~v1_relat_1(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.20/0.38  cnf(c_0_9, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_10, negated_conjecture, (v2_wellord1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  fof(c_0_12, plain, ![X14, X15, X16]:((~r1_tarski(k1_wellord1(X16,X14),k1_wellord1(X16,X15))|(X14=X15|r2_hidden(X14,k1_wellord1(X16,X15)))|(~v2_wellord1(X16)|~r2_hidden(X14,k3_relat_1(X16))|~r2_hidden(X15,k3_relat_1(X16)))|~v1_relat_1(X16))&((X14!=X15|r1_tarski(k1_wellord1(X16,X14),k1_wellord1(X16,X15))|(~v2_wellord1(X16)|~r2_hidden(X14,k3_relat_1(X16))|~r2_hidden(X15,k3_relat_1(X16)))|~v1_relat_1(X16))&(~r2_hidden(X14,k1_wellord1(X16,X15))|r1_tarski(k1_wellord1(X16,X14),k1_wellord1(X16,X15))|(~v2_wellord1(X16)|~r2_hidden(X14,k3_relat_1(X16))|~r2_hidden(X15,k3_relat_1(X16)))|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_wellord1])])])).
% 0.20/0.38  cnf(c_0_13, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk4_0,k3_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v6_relat_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.20/0.38  cnf(c_0_16, plain, (r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))|X1!=X2|~v2_wellord1(X3)|~r2_hidden(X1,k3_relat_1(X3))|~r2_hidden(X2,k3_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_17, plain, ![X11, X12, X13]:((~r2_hidden(k4_tarski(X11,X12),X13)|r1_tarski(k1_wellord1(X13,X11),k1_wellord1(X13,X12))|(~v2_wellord1(X13)|~r2_hidden(X11,k3_relat_1(X13))|~r2_hidden(X12,k3_relat_1(X13)))|~v1_relat_1(X13))&(~r1_tarski(k1_wellord1(X13,X11),k1_wellord1(X13,X12))|r2_hidden(k4_tarski(X11,X12),X13)|(~v2_wellord1(X13)|~r2_hidden(X11,k3_relat_1(X13))|~r2_hidden(X12,k3_relat_1(X13)))|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_wellord1])])])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (X1=esk4_0|r2_hidden(k4_tarski(X1,esk4_0),esk5_0)|r2_hidden(k4_tarski(esk4_0,X1),esk5_0)|~r2_hidden(X1,k3_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_11])]), c_0_15])])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_0,k3_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (~r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_21, plain, (r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X2))|~r2_hidden(X2,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, plain, (r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))|~r2_hidden(k4_tarski(X1,X2),X3)|~v2_wellord1(X3)|~r2_hidden(X1,k3_relat_1(X3))|~r2_hidden(X2,k3_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (esk4_0=esk3_0|r2_hidden(k4_tarski(esk4_0,esk3_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (X1!=esk4_0|~r2_hidden(X1,k1_wellord1(esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X2,X3),X1)|~r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(k1_wellord1(esk5_0,X1),k1_wellord1(esk5_0,X1))|~r2_hidden(X1,k3_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_10]), c_0_11])])).
% 0.20/0.38  cnf(c_0_27, plain, (X2=X3|r2_hidden(X2,k1_wellord1(X1,X3))|~r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (esk4_0=esk3_0|r1_tarski(k1_wellord1(esk5_0,esk4_0),k1_wellord1(esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19]), c_0_14]), c_0_10]), c_0_11])])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk4_0,k1_wellord1(esk5_0,esk3_0))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,X1),esk5_0)|~r2_hidden(X1,k3_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_10]), c_0_11])])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (esk4_0=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19]), c_0_14]), c_0_10]), c_0_11])]), c_0_29])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_19])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_31]), c_0_32])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 34
% 0.20/0.38  # Proof object clause steps            : 23
% 0.20/0.38  # Proof object formula steps           : 11
% 0.20/0.38  # Proof object conjectures             : 19
% 0.20/0.38  # Proof object clause conjectures      : 16
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 5
% 0.20/0.38  # Proof object generating inferences   : 8
% 0.20/0.38  # Proof object simplifying inferences  : 28
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 5
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 24
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 24
% 0.20/0.38  # Processed clauses                    : 68
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 68
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 10
% 0.20/0.38  # Generated clauses                    : 36
% 0.20/0.38  # ...of the previous two non-trivial   : 27
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 34
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 32
% 0.20/0.38  #    Positive orientable unit clauses  : 11
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 20
% 0.20/0.38  # Current number of unprocessed clauses: 3
% 0.20/0.38  # ...number of literals in the above   : 16
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 34
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 416
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 59
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 39
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3037
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
