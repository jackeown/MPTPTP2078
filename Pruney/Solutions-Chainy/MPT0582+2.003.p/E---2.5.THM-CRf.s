%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  86 expanded)
%              Number of clauses        :   22 (  32 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 ( 391 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(k1_relat_1(X3),X1)
              & r1_tarski(X3,X2) )
           => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(k1_relat_1(X3),X1)
                & r1_tarski(X3,X2) )
             => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_relat_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(k4_tarski(X11,X12),X6)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk1_3(X6,X7,X8),X7)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k7_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_8,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ r1_tarski(k1_relat_1(X28),X27)
      | k7_relat_1(X28,X27) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(k1_relat_1(esk7_0),esk5_0)
    & r1_tarski(esk7_0,esk6_0)
    & ~ r1_tarski(esk7_0,k7_relat_1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r1_tarski(X15,X16)
        | ~ r2_hidden(k4_tarski(X17,X18),X15)
        | r2_hidden(k4_tarski(X17,X18),X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)
        | r1_tarski(X15,X19)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)
        | r1_tarski(X15,X19)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k7_relat_1(esk7_0,esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k7_relat_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(esk7_0,k7_relat_1(esk6_0,esk5_0)),esk4_2(esk7_0,k7_relat_1(esk6_0,esk5_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k7_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(esk3_2(X1,k7_relat_1(X2,X3)),esk4_2(X1,k7_relat_1(X2,X3))),X2)
    | ~ r2_hidden(esk3_2(X1,k7_relat_1(X2,X3)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_2(esk7_0,k7_relat_1(esk6_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_2(esk7_0,k7_relat_1(esk6_0,esk5_0)),esk4_2(esk7_0,k7_relat_1(esk6_0,esk5_0))),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_14]),c_0_27])]),c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk6_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.41  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t186_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_relat_1)).
% 0.20/0.41  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 0.20/0.41  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.41  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.20/0.41  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.20/0.41  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t186_relat_1])).
% 0.20/0.41  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(X9,X10),X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&(~r2_hidden(X11,X7)|~r2_hidden(k4_tarski(X11,X12),X6)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk1_3(X6,X7,X8),X7)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6))|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&((r2_hidden(esk1_3(X6,X7,X8),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.20/0.41  fof(c_0_7, plain, ![X22, X23]:(~v1_relat_1(X22)|v1_relat_1(k7_relat_1(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.41  fof(c_0_8, plain, ![X27, X28]:(~v1_relat_1(X28)|(~r1_tarski(k1_relat_1(X28),X27)|k7_relat_1(X28,X27)=X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.20/0.41  fof(c_0_9, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&((r1_tarski(k1_relat_1(esk7_0),esk5_0)&r1_tarski(esk7_0,esk6_0))&~r1_tarski(esk7_0,k7_relat_1(esk6_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.41  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k7_relat_1(X5,X2)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_11, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_12, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_13, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  fof(c_0_15, plain, ![X15, X16, X17, X18, X19]:((~r1_tarski(X15,X16)|(~r2_hidden(k4_tarski(X17,X18),X15)|r2_hidden(k4_tarski(X17,X18),X16))|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X15)|r1_tarski(X15,X19)|~v1_relat_1(X15))&(~r2_hidden(k4_tarski(esk3_2(X15,X19),esk4_2(X15,X19)),X19)|r1_tarski(X15,X19)|~v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.20/0.41  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,X3),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X5!=k7_relat_1(X4,X2)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))|~v1_relat_1(X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (k7_relat_1(esk7_0,esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (~r1_tarski(esk7_0,k7_relat_1(esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_11])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X1,X2),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_14])])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk3_2(esk7_0,k7_relat_1(esk6_0,esk5_0)),esk4_2(esk7_0,k7_relat_1(esk6_0,esk5_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_14])])).
% 0.20/0.41  cnf(c_0_25, plain, (r1_tarski(X1,k7_relat_1(X2,X3))|~r2_hidden(k4_tarski(esk3_2(X1,k7_relat_1(X2,X3)),esk4_2(X1,k7_relat_1(X2,X3))),X2)|~r2_hidden(esk3_2(X1,k7_relat_1(X2,X3)),X3)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_2(esk7_0,k7_relat_1(esk6_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (~r2_hidden(k4_tarski(esk3_2(esk7_0,k7_relat_1(esk6_0,esk5_0)),esk4_2(esk7_0,k7_relat_1(esk6_0,esk5_0))),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_14]), c_0_27])]), c_0_19])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk6_0)|~r2_hidden(k4_tarski(X1,X2),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_14])])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 33
% 0.20/0.41  # Proof object clause steps            : 22
% 0.20/0.41  # Proof object formula steps           : 11
% 0.20/0.41  # Proof object conjectures             : 15
% 0.20/0.41  # Proof object clause conjectures      : 12
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 12
% 0.20/0.41  # Proof object initial formulas used   : 5
% 0.20/0.41  # Proof object generating inferences   : 8
% 0.20/0.41  # Proof object simplifying inferences  : 18
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 7
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 18
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 18
% 0.20/0.41  # Processed clauses                    : 382
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 147
% 0.20/0.41  # ...remaining for further processing  : 235
% 0.20/0.41  # Other redundant clauses eliminated   : 3
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 36
% 0.20/0.41  # Backward-rewritten                   : 3
% 0.20/0.41  # Generated clauses                    : 1158
% 0.20/0.41  # ...of the previous two non-trivial   : 972
% 0.20/0.41  # Contextual simplify-reflections      : 13
% 0.20/0.41  # Paramodulations                      : 1137
% 0.20/0.41  # Factorizations                       : 18
% 0.20/0.41  # Equation resolutions                 : 3
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 175
% 0.20/0.41  #    Positive orientable unit clauses  : 19
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 154
% 0.20/0.41  # Current number of unprocessed clauses: 619
% 0.20/0.41  # ...number of literals in the above   : 2894
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 57
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4924
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 3302
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 196
% 0.20/0.41  # Unit Clause-clause subsumption calls : 126
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 6
% 0.20/0.41  # BW rewrite match successes           : 3
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 29271
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.066 s
% 0.20/0.42  # System time              : 0.004 s
% 0.20/0.42  # Total time               : 0.071 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
