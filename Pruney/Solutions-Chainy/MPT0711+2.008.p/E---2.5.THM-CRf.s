%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:36 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 294 expanded)
%              Number of clauses        :   30 ( 107 expanded)
%              Number of leaves         :    6 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 (1471 expanded)
%              Number of equality atoms :   51 ( 531 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t166_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( k1_relat_1(X1) = k1_relat_1(X2)
                & ! [X4] :
                    ( r2_hidden(X4,X3)
                   => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) )
             => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t68_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = k3_xboole_0(k1_relat_1(X3),X1)
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) )
           => X2 = k7_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( k1_relat_1(X1) = k1_relat_1(X2)
                  & ! [X4] :
                      ( r2_hidden(X4,X3)
                     => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) )
               => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t166_funct_1])).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | k1_relat_1(k7_relat_1(X9,X8)) = k3_xboole_0(k1_relat_1(X9),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_8,negated_conjecture,(
    ! [X22] :
      ( v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & k1_relat_1(esk2_0) = k1_relat_1(esk3_0)
      & ( ~ r2_hidden(X22,esk4_0)
        | k1_funct_1(esk2_0,X22) = k1_funct_1(esk3_0,X22) )
      & k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ( r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))
        | k1_relat_1(X13) != k3_xboole_0(k1_relat_1(X14),X12)
        | X13 = k7_relat_1(X14,X12)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk1_3(X12,X13,X14)) != k1_funct_1(X14,esk1_3(X12,X13,X14))
        | k1_relat_1(X13) != k3_xboole_0(k1_relat_1(X14),X12)
        | X13 = k7_relat_1(X14,X12)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).

cnf(c_0_10,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X10,X11] :
      ( ( v1_relat_1(k7_relat_1(X10,X11))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k7_relat_1(X10,X11))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))
    | X2 = k7_relat_1(X3,X1)
    | k1_relat_1(X2) != k3_xboole_0(k1_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk3_0),X1) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk2_0) = k1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r2_hidden(X16,k1_relat_1(k7_relat_1(X18,X17)))
      | k1_funct_1(k7_relat_1(X18,X17),X16) = k1_funct_1(X18,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k7_relat_1(esk3_0,X2)
    | r2_hidden(esk1_3(X2,X1,esk3_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(k7_relat_1(esk3_0,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])]),c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_18]),c_0_19]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_18])])).

fof(c_0_26,plain,(
    ! [X5,X6,X7] :
      ( ( r2_hidden(X5,X6)
        | ~ r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(X5,k1_relat_1(X7))
        | ~ r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X5,X6)
        | ~ r2_hidden(X5,k1_relat_1(X7))
        | r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_27,plain,
    ( X1 = k7_relat_1(X3,X2)
    | k1_funct_1(X1,esk1_3(X2,X1,X3)) != k1_funct_1(X3,esk1_3(X2,X1,X3))
    | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = k7_relat_1(esk3_0,X2)
    | r2_hidden(esk1_3(X2,k7_relat_1(esk2_0,X1),esk3_0),k1_relat_1(k7_relat_1(esk3_0,X1)))
    | k1_relat_1(k7_relat_1(esk3_0,X1)) != k1_relat_1(k7_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k7_relat_1(esk3_0,X2)
    | k1_funct_1(X1,esk1_3(X2,X1,esk3_0)) != k1_funct_1(esk3_0,esk1_3(X2,X1,esk3_0))
    | k1_relat_1(X1) != k1_relat_1(k7_relat_1(esk3_0,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_11])]),c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,X1),X2) = k1_funct_1(esk2_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_18])]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = k7_relat_1(esk3_0,X1)
    | r2_hidden(esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0),k1_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = k7_relat_1(esk3_0,X2)
    | k1_funct_1(k7_relat_1(esk2_0,X1),esk1_3(X2,k7_relat_1(esk2_0,X1),esk3_0)) != k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk2_0,X1),esk3_0))
    | k1_relat_1(k7_relat_1(esk3_0,X1)) != k1_relat_1(k7_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,X1),esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0)) = k1_funct_1(esk2_0,esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0))
    | k7_relat_1(esk2_0,X1) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = k7_relat_1(esk3_0,X1)
    | r2_hidden(esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = k7_relat_1(esk3_0,X1)
    | k1_funct_1(esk2_0,esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0)) != k1_funct_1(esk3_0,esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk2_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0)) = k1_funct_1(esk3_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:57:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.12/0.39  # and selection function SelectCQIAr.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.027 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t166_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_funct_1)).
% 0.12/0.39  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.12/0.39  fof(t68_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=k3_xboole_0(k1_relat_1(X3),X1)&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))=>X2=k7_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_funct_1)).
% 0.12/0.39  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.12/0.39  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 0.12/0.39  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.12/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t166_funct_1])).
% 0.12/0.39  fof(c_0_7, plain, ![X8, X9]:(~v1_relat_1(X9)|k1_relat_1(k7_relat_1(X9,X8))=k3_xboole_0(k1_relat_1(X9),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.12/0.39  fof(c_0_8, negated_conjecture, ![X22]:((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((k1_relat_1(esk2_0)=k1_relat_1(esk3_0)&(~r2_hidden(X22,esk4_0)|k1_funct_1(esk2_0,X22)=k1_funct_1(esk3_0,X22)))&k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.12/0.39  fof(c_0_9, plain, ![X12, X13, X14]:((r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))|k1_relat_1(X13)!=k3_xboole_0(k1_relat_1(X14),X12)|X13=k7_relat_1(X14,X12)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk1_3(X12,X13,X14))!=k1_funct_1(X14,esk1_3(X12,X13,X14))|k1_relat_1(X13)!=k3_xboole_0(k1_relat_1(X14),X12)|X13=k7_relat_1(X14,X12)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).
% 0.12/0.39  cnf(c_0_10, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.39  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  fof(c_0_12, plain, ![X10, X11]:((v1_relat_1(k7_relat_1(X10,X11))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k7_relat_1(X10,X11))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.12/0.39  cnf(c_0_13, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X2))|X2=k7_relat_1(X3,X1)|k1_relat_1(X2)!=k3_xboole_0(k1_relat_1(X3),X1)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_14, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_15, negated_conjecture, (k3_xboole_0(k1_relat_1(esk3_0),X1)=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.39  cnf(c_0_16, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_19, negated_conjecture, (k1_relat_1(esk2_0)=k1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_20, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  fof(c_0_21, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r2_hidden(X16,k1_relat_1(k7_relat_1(X18,X17)))|k1_funct_1(k7_relat_1(X18,X17),X16)=k1_funct_1(X18,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.12/0.39  cnf(c_0_22, negated_conjecture, (X1=k7_relat_1(esk3_0,X2)|r2_hidden(esk1_3(X2,X1,esk3_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(k7_relat_1(esk3_0,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_11])]), c_0_15])).
% 0.12/0.39  cnf(c_0_23, negated_conjecture, (v1_funct_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_18]), c_0_19]), c_0_15])).
% 0.12/0.39  cnf(c_0_25, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_18])])).
% 0.12/0.39  fof(c_0_26, plain, ![X5, X6, X7]:(((r2_hidden(X5,X6)|~r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))|~v1_relat_1(X7))&(r2_hidden(X5,k1_relat_1(X7))|~r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))|~v1_relat_1(X7)))&(~r2_hidden(X5,X6)|~r2_hidden(X5,k1_relat_1(X7))|r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.12/0.39  cnf(c_0_27, plain, (X1=k7_relat_1(X3,X2)|k1_funct_1(X1,esk1_3(X2,X1,X3))!=k1_funct_1(X3,esk1_3(X2,X1,X3))|k1_relat_1(X1)!=k3_xboole_0(k1_relat_1(X3),X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_28, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.39  cnf(c_0_29, negated_conjecture, (k7_relat_1(esk2_0,X1)=k7_relat_1(esk3_0,X2)|r2_hidden(esk1_3(X2,k7_relat_1(esk2_0,X1),esk3_0),k1_relat_1(k7_relat_1(esk3_0,X1)))|k1_relat_1(k7_relat_1(esk3_0,X1))!=k1_relat_1(k7_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24]), c_0_25])])).
% 0.12/0.39  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (X1=k7_relat_1(esk3_0,X2)|k1_funct_1(X1,esk1_3(X2,X1,esk3_0))!=k1_funct_1(esk3_0,esk1_3(X2,X1,esk3_0))|k1_relat_1(X1)!=k1_relat_1(k7_relat_1(esk3_0,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_14]), c_0_11])]), c_0_15])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (k1_funct_1(k7_relat_1(esk2_0,X1),X2)=k1_funct_1(esk2_0,X2)|~r2_hidden(X2,k1_relat_1(k7_relat_1(esk3_0,X1)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_17]), c_0_18])]), c_0_24])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (k7_relat_1(esk2_0,X1)=k7_relat_1(esk3_0,X1)|r2_hidden(esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0),k1_relat_1(k7_relat_1(esk3_0,X1)))), inference(er,[status(thm)],[c_0_29])).
% 0.12/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_11])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (k7_relat_1(esk2_0,X1)=k7_relat_1(esk3_0,X2)|k1_funct_1(k7_relat_1(esk2_0,X1),esk1_3(X2,k7_relat_1(esk2_0,X1),esk3_0))!=k1_funct_1(esk3_0,esk1_3(X2,k7_relat_1(esk2_0,X1),esk3_0))|k1_relat_1(k7_relat_1(esk3_0,X1))!=k1_relat_1(k7_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_24]), c_0_25])])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (k1_funct_1(k7_relat_1(esk2_0,X1),esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0))=k1_funct_1(esk2_0,esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0))|k7_relat_1(esk2_0,X1)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk2_0,X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (k7_relat_1(esk2_0,X1)=k7_relat_1(esk3_0,X1)|r2_hidden(esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (k7_relat_1(esk2_0,X1)=k7_relat_1(esk3_0,X1)|k1_funct_1(esk2_0,esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0))!=k1_funct_1(esk3_0,esk1_3(X1,k7_relat_1(esk2_0,X1),esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk2_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0))=k1_funct_1(esk3_0,esk1_3(esk4_0,k7_relat_1(esk2_0,esk4_0),esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_39]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 43
% 0.12/0.39  # Proof object clause steps            : 30
% 0.12/0.39  # Proof object formula steps           : 13
% 0.12/0.39  # Proof object conjectures             : 26
% 0.12/0.39  # Proof object clause conjectures      : 23
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 14
% 0.12/0.39  # Proof object initial formulas used   : 6
% 0.12/0.39  # Proof object generating inferences   : 16
% 0.12/0.39  # Proof object simplifying inferences  : 24
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 6
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 16
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 16
% 0.12/0.39  # Processed clauses                    : 200
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 31
% 0.12/0.39  # ...remaining for further processing  : 169
% 0.12/0.39  # Other redundant clauses eliminated   : 0
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 2
% 0.12/0.39  # Backward-rewritten                   : 12
% 0.12/0.39  # Generated clauses                    : 606
% 0.12/0.39  # ...of the previous two non-trivial   : 614
% 0.12/0.39  # Contextual simplify-reflections      : 7
% 0.12/0.39  # Paramodulations                      : 602
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 4
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 139
% 0.12/0.39  #    Positive orientable unit clauses  : 43
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 1
% 0.12/0.39  #    Non-unit-clauses                  : 95
% 0.12/0.39  # Current number of unprocessed clauses: 446
% 0.12/0.39  # ...number of literals in the above   : 1213
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 30
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 884
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 736
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 40
% 0.12/0.39  # Unit Clause-clause subsumption calls : 6
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 185
% 0.12/0.39  # BW rewrite match successes           : 7
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 25834
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.047 s
% 0.12/0.39  # System time              : 0.006 s
% 0.12/0.39  # Total time               : 0.053 s
% 0.12/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
