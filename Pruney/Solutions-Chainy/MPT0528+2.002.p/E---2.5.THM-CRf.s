%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:06 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  73 expanded)
%              Number of clauses        :   16 (  32 expanded)
%              Number of leaves         :    3 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 303 expanded)
%              Number of equality atoms :   22 (  67 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t128_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

fof(c_0_3,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X10,X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(X9,X10),X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X12,X6)
        | ~ r2_hidden(k4_tarski(X11,X12),X7)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X6)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_4,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k8_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t128_relat_1])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & k8_relat_1(esk3_0,k8_relat_1(esk3_0,esk4_0)) != k8_relat_1(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( X1 = k8_relat_1(X2,k8_relat_1(X3,X4))
    | r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,X4),X1),esk2_3(X2,k8_relat_1(X3,X4),X1)),k8_relat_1(X3,X4))
    | r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,X4),X1),esk2_3(X2,k8_relat_1(X3,X4),X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( X1 = k8_relat_1(X2,k8_relat_1(X3,esk4_0))
    | r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),X1),esk2_3(X2,k8_relat_1(X3,esk4_0),X1)),k8_relat_1(X3,esk4_0))
    | r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),X1),esk2_3(X2,k8_relat_1(X3,esk4_0),X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( k8_relat_1(X1,X2) = k8_relat_1(X3,k8_relat_1(X4,esk4_0))
    | r2_hidden(k4_tarski(esk1_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2)),esk2_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2))),k8_relat_1(X4,esk4_0))
    | r2_hidden(k4_tarski(esk1_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2)),esk2_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2))),k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,negated_conjecture,
    ( k8_relat_1(X1,esk4_0) = k8_relat_1(X2,k8_relat_1(X3,esk4_0))
    | r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0)),esk2_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0))),k8_relat_1(X1,esk4_0))
    | r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0)),esk2_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0))),k8_relat_1(X3,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k8_relat_1(X2,X4))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X2,esk4_0)) = k8_relat_1(X2,esk4_0)
    | r2_hidden(k4_tarski(esk1_3(X1,k8_relat_1(X2,esk4_0),k8_relat_1(X2,esk4_0)),esk2_3(X1,k8_relat_1(X2,esk4_0),k8_relat_1(X2,esk4_0))),k8_relat_1(X2,esk4_0)) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( X3 = k8_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_18,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X2,esk4_0)) = k8_relat_1(X2,esk4_0)
    | r2_hidden(esk2_3(X1,k8_relat_1(X2,esk4_0),k8_relat_1(X2,esk4_0)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10])])).

cnf(c_0_19,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X1,esk4_0)) = k8_relat_1(X1,esk4_0)
    | ~ v1_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k8_relat_1(esk3_0,k8_relat_1(esk3_0,esk4_0)) != k8_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X1,esk4_0)) = k8_relat_1(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_7]),c_0_10])])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.14/0.40  # and selection function SelectVGNonCR.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.027 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 0.14/0.40  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.14/0.40  fof(t128_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_relat_1)).
% 0.14/0.40  fof(c_0_3, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X10,X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(X9,X10),X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(X12,X6)|~r2_hidden(k4_tarski(X11,X12),X7)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk2_3(X6,X7,X8),X6)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7))|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(esk2_3(X6,X7,X8),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.14/0.40  fof(c_0_4, plain, ![X15, X16]:(~v1_relat_1(X16)|v1_relat_1(k8_relat_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.14/0.40  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2))), inference(assume_negation,[status(cth)],[t128_relat_1])).
% 0.14/0.40  cnf(c_0_6, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.14/0.40  cnf(c_0_7, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.40  fof(c_0_8, negated_conjecture, (v1_relat_1(esk4_0)&k8_relat_1(esk3_0,k8_relat_1(esk3_0,esk4_0))!=k8_relat_1(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.40  cnf(c_0_9, plain, (X1=k8_relat_1(X2,k8_relat_1(X3,X4))|r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,X4),X1),esk2_3(X2,k8_relat_1(X3,X4),X1)),k8_relat_1(X3,X4))|r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,X4),X1),esk2_3(X2,k8_relat_1(X3,X4),X1)),X1)|~v1_relat_1(X1)|~v1_relat_1(X4)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.14/0.40  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.40  cnf(c_0_11, negated_conjecture, (X1=k8_relat_1(X2,k8_relat_1(X3,esk4_0))|r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),X1),esk2_3(X2,k8_relat_1(X3,esk4_0),X1)),k8_relat_1(X3,esk4_0))|r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),X1),esk2_3(X2,k8_relat_1(X3,esk4_0),X1)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.40  cnf(c_0_12, negated_conjecture, (k8_relat_1(X1,X2)=k8_relat_1(X3,k8_relat_1(X4,esk4_0))|r2_hidden(k4_tarski(esk1_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2)),esk2_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2))),k8_relat_1(X4,esk4_0))|r2_hidden(k4_tarski(esk1_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2)),esk2_3(X3,k8_relat_1(X4,esk4_0),k8_relat_1(X1,X2))),k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_11, c_0_7])).
% 0.14/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X4!=k8_relat_1(X2,X5)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.14/0.40  cnf(c_0_14, negated_conjecture, (k8_relat_1(X1,esk4_0)=k8_relat_1(X2,k8_relat_1(X3,esk4_0))|r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0)),esk2_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0))),k8_relat_1(X1,esk4_0))|r2_hidden(k4_tarski(esk1_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0)),esk2_3(X2,k8_relat_1(X3,esk4_0),k8_relat_1(X1,esk4_0))),k8_relat_1(X3,esk4_0))), inference(spm,[status(thm)],[c_0_12, c_0_10])).
% 0.14/0.40  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k8_relat_1(X2,X4))|~v1_relat_1(X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_7])).
% 0.14/0.40  cnf(c_0_16, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X2,esk4_0))=k8_relat_1(X2,esk4_0)|r2_hidden(k4_tarski(esk1_3(X1,k8_relat_1(X2,esk4_0),k8_relat_1(X2,esk4_0)),esk2_3(X1,k8_relat_1(X2,esk4_0),k8_relat_1(X2,esk4_0))),k8_relat_1(X2,esk4_0))), inference(ef,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_17, plain, (X3=k8_relat_1(X1,X2)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.14/0.40  cnf(c_0_18, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X2,esk4_0))=k8_relat_1(X2,esk4_0)|r2_hidden(esk2_3(X1,k8_relat_1(X2,esk4_0),k8_relat_1(X2,esk4_0)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_10])])).
% 0.14/0.40  cnf(c_0_19, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X1,esk4_0))=k8_relat_1(X1,esk4_0)|~v1_relat_1(k8_relat_1(X1,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_16])).
% 0.14/0.40  cnf(c_0_20, negated_conjecture, (k8_relat_1(esk3_0,k8_relat_1(esk3_0,esk4_0))!=k8_relat_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.40  cnf(c_0_21, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X1,esk4_0))=k8_relat_1(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_7]), c_0_10])])).
% 0.14/0.40  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 23
% 0.14/0.40  # Proof object clause steps            : 16
% 0.14/0.40  # Proof object formula steps           : 7
% 0.14/0.40  # Proof object conjectures             : 13
% 0.14/0.40  # Proof object clause conjectures      : 10
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 6
% 0.14/0.40  # Proof object initial formulas used   : 3
% 0.14/0.40  # Proof object generating inferences   : 9
% 0.14/0.40  # Proof object simplifying inferences  : 8
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 3
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 9
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 9
% 0.14/0.40  # Processed clauses                    : 256
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 67
% 0.14/0.40  # ...remaining for further processing  : 189
% 0.14/0.40  # Other redundant clauses eliminated   : 0
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 42
% 0.14/0.40  # Backward-rewritten                   : 2
% 0.14/0.40  # Generated clauses                    : 405
% 0.14/0.40  # ...of the previous two non-trivial   : 346
% 0.14/0.40  # Contextual simplify-reflections      : 5
% 0.14/0.40  # Paramodulations                      : 384
% 0.14/0.40  # Factorizations                       : 18
% 0.14/0.40  # Equation resolutions                 : 3
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 136
% 0.14/0.40  #    Positive orientable unit clauses  : 2
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 0
% 0.14/0.40  #    Non-unit-clauses                  : 134
% 0.14/0.40  # Current number of unprocessed clauses: 95
% 0.14/0.40  # ...number of literals in the above   : 407
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 53
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 7215
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 1913
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 114
% 0.14/0.40  # Unit Clause-clause subsumption calls : 104
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 11
% 0.14/0.40  # BW rewrite match successes           : 2
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 20614
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.051 s
% 0.14/0.40  # System time              : 0.007 s
% 0.14/0.40  # Total time               : 0.058 s
% 0.14/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
