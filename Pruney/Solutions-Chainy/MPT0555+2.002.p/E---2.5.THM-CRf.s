%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:01 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   34 (  65 expanded)
%              Number of clauses        :   21 (  27 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 191 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t157_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t106_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t157_relat_1])).

fof(c_0_7,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k2_relat_1(k7_relat_1(X14,X13)) = k9_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,esk3_0)
    & ~ r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | v1_relat_1(k7_relat_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_10,plain,(
    ! [X9,X10,X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(k7_relat_1(X11,X9),k7_relat_1(X12,X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_relat_1])])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(k1_relat_1(X15),k1_relat_1(X16))
        | ~ r1_tarski(X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) )
      & ( r1_tarski(k2_relat_1(X15),k2_relat_1(X16))
        | ~ r1_tarski(X15,X16)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_12,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(esk3_0,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k9_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k7_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_22])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X2))
    | ~ r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n002.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 14:19:51 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  # Version: 2.5pre002
% 0.11/0.31  # No SInE strategy applied
% 0.11/0.31  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.17/0.35  # and selection function PSelectSmallestOrientable.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.027 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t157_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 0.17/0.35  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.17/0.35  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.17/0.35  fof(t106_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 0.17/0.35  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.17/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.17/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)))))), inference(assume_negation,[status(cth)],[t157_relat_1])).
% 0.17/0.35  fof(c_0_7, plain, ![X13, X14]:(~v1_relat_1(X14)|k2_relat_1(k7_relat_1(X14,X13))=k9_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.17/0.35  fof(c_0_8, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(r1_tarski(esk2_0,esk3_0)&~r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.17/0.35  fof(c_0_9, plain, ![X7, X8]:(~v1_relat_1(X7)|v1_relat_1(k7_relat_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.17/0.35  fof(c_0_10, plain, ![X9, X10, X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|(~r1_tarski(X11,X12)|~r1_tarski(X9,X10)|r1_tarski(k7_relat_1(X11,X9),k7_relat_1(X12,X10))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_relat_1])])])).
% 0.17/0.35  fof(c_0_11, plain, ![X15, X16]:((r1_tarski(k1_relat_1(X15),k1_relat_1(X16))|~r1_tarski(X15,X16)|~v1_relat_1(X16)|~v1_relat_1(X15))&(r1_tarski(k2_relat_1(X15),k2_relat_1(X16))|~r1_tarski(X15,X16)|~v1_relat_1(X16)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.17/0.35  cnf(c_0_12, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.35  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.35  cnf(c_0_14, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.35  cnf(c_0_15, plain, (r1_tarski(k7_relat_1(X1,X3),k7_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  fof(c_0_16, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.17/0.35  cnf(c_0_17, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.35  cnf(c_0_18, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.17/0.35  cnf(c_0_19, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.17/0.35  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.35  cnf(c_0_21, negated_conjecture, (r1_tarski(k7_relat_1(X1,X2),k7_relat_1(esk3_0,X3))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_15, c_0_13])).
% 0.17/0.35  cnf(c_0_22, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.35  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.35  cnf(c_0_24, negated_conjecture, (r1_tarski(k2_relat_1(X1),k9_relat_1(esk3_0,X2))|~v1_relat_1(X1)|~r1_tarski(X1,k7_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.17/0.35  cnf(c_0_25, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_14, c_0_20])).
% 0.17/0.35  cnf(c_0_26, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_20])).
% 0.17/0.35  cnf(c_0_27, negated_conjecture, (r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X2))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_22])])).
% 0.17/0.35  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.17/0.35  cnf(c_0_29, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X2))|~r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.17/0.35  cnf(c_0_30, negated_conjecture, (r1_tarski(k7_relat_1(esk2_0,X1),k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.17/0.35  cnf(c_0_31, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk1_0),k9_relat_1(esk3_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.35  cnf(c_0_32, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.17/0.35  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 34
% 0.17/0.35  # Proof object clause steps            : 21
% 0.17/0.35  # Proof object formula steps           : 13
% 0.17/0.35  # Proof object conjectures             : 18
% 0.17/0.35  # Proof object clause conjectures      : 15
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 9
% 0.17/0.35  # Proof object initial formulas used   : 6
% 0.17/0.35  # Proof object generating inferences   : 10
% 0.17/0.35  # Proof object simplifying inferences  : 8
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 6
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 12
% 0.17/0.35  # Removed in clause preprocessing      : 0
% 0.17/0.35  # Initial clauses in saturation        : 12
% 0.17/0.35  # Processed clauses                    : 138
% 0.17/0.35  # ...of these trivial                  : 1
% 0.17/0.35  # ...subsumed                          : 13
% 0.17/0.35  # ...remaining for further processing  : 124
% 0.17/0.35  # Other redundant clauses eliminated   : 2
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 0
% 0.17/0.35  # Backward-rewritten                   : 1
% 0.17/0.35  # Generated clauses                    : 476
% 0.17/0.35  # ...of the previous two non-trivial   : 464
% 0.17/0.35  # Contextual simplify-reflections      : 0
% 0.17/0.35  # Paramodulations                      : 474
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 2
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 110
% 0.17/0.35  #    Positive orientable unit clauses  : 58
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 0
% 0.17/0.35  #    Non-unit-clauses                  : 52
% 0.17/0.35  # Current number of unprocessed clauses: 349
% 0.17/0.35  # ...number of literals in the above   : 661
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 12
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 153
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 129
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 13
% 0.17/0.35  # Unit Clause-clause subsumption calls : 8
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 62
% 0.17/0.35  # BW rewrite match successes           : 1
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 9935
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.033 s
% 0.17/0.35  # System time              : 0.007 s
% 0.17/0.35  # Total time               : 0.040 s
% 0.17/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
