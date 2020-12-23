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
% DateTime   : Thu Dec  3 10:55:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 237 expanded)
%              Number of clauses        :   34 (  98 expanded)
%              Number of leaves         :    8 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  184 (1256 expanded)
%              Number of equality atoms :   13 (  54 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
            <=> ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
              <=> ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t171_funct_1])).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | k1_relat_1(k5_relat_1(X17,X18)) = k10_relat_1(X17,k1_relat_1(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & ( ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
      | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0))
      | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) )
    & ( r1_tarski(esk5_0,k1_relat_1(esk3_0))
      | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) )
    & ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
      | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X22,k1_relat_1(X19))
        | ~ r2_hidden(X22,X21)
        | X21 != k10_relat_1(X19,X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(k1_funct_1(X19,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k10_relat_1(X19,X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(X23,k1_relat_1(X19))
        | ~ r2_hidden(k1_funct_1(X19,X23),X20)
        | r2_hidden(X23,X21)
        | X21 != k10_relat_1(X19,X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(esk2_3(X19,X24,X25),X25)
        | ~ r2_hidden(esk2_3(X19,X24,X25),k1_relat_1(X19))
        | ~ r2_hidden(k1_funct_1(X19,esk2_3(X19,X24,X25)),X24)
        | X25 = k10_relat_1(X19,X24)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk2_3(X19,X24,X25),k1_relat_1(X19))
        | r2_hidden(esk2_3(X19,X24,X25),X25)
        | X25 = k10_relat_1(X19,X24)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(k1_funct_1(X19,esk2_3(X19,X24,X25)),X24)
        | r2_hidden(esk2_3(X19,X24,X25),X25)
        | X25 = k10_relat_1(X19,X24)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k10_relat_1(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ r1_tarski(X29,k1_relat_1(X31))
      | ~ r1_tarski(k9_relat_1(X31,X29),X30)
      | r1_tarski(X29,k10_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_13])])).

cnf(c_0_30,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_33,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | r1_tarski(k9_relat_1(X28,k10_relat_1(X28,X27)),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_34,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(k9_relat_1(X16,X14),k9_relat_1(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26]),c_0_13])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_38,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))
    | ~ r1_tarski(esk5_0,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_13])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_31])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_41])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.38  # and selection function SelectNewComplexAHP.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.013 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 0.19/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 0.19/0.38  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.19/0.38  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.19/0.38  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.19/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.19/0.38  fof(c_0_9, plain, ![X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|k1_relat_1(k5_relat_1(X17,X18))=k10_relat_1(X17,k1_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|(~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))))&((r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0))))&(r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  cnf(c_0_12, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_18, plain, ![X19, X20, X21, X22, X23, X24, X25]:((((r2_hidden(X22,k1_relat_1(X19))|~r2_hidden(X22,X21)|X21!=k10_relat_1(X19,X20)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(r2_hidden(k1_funct_1(X19,X22),X20)|~r2_hidden(X22,X21)|X21!=k10_relat_1(X19,X20)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&(~r2_hidden(X23,k1_relat_1(X19))|~r2_hidden(k1_funct_1(X19,X23),X20)|r2_hidden(X23,X21)|X21!=k10_relat_1(X19,X20)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&((~r2_hidden(esk2_3(X19,X24,X25),X25)|(~r2_hidden(esk2_3(X19,X24,X25),k1_relat_1(X19))|~r2_hidden(k1_funct_1(X19,esk2_3(X19,X24,X25)),X24))|X25=k10_relat_1(X19,X24)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&((r2_hidden(esk2_3(X19,X24,X25),k1_relat_1(X19))|r2_hidden(esk2_3(X19,X24,X25),X25)|X25=k10_relat_1(X19,X24)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(r2_hidden(k1_funct_1(X19,esk2_3(X19,X24,X25)),X24)|r2_hidden(esk2_3(X19,X24,X25),X25)|X25=k10_relat_1(X19,X24)|(~v1_relat_1(X19)|~v1_funct_1(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k10_relat_1(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_24, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_27, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~r1_tarski(X29,k1_relat_1(X31))|~r1_tarski(k9_relat_1(X31,X29),X30)|r1_tarski(X29,k10_relat_1(X31,X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.19/0.38  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),k1_relat_1(esk3_0))|r1_tarski(esk5_0,k1_relat_1(esk3_0))|r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_13])])).
% 0.19/0.38  cnf(c_0_30, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_33, plain, ![X27, X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|r1_tarski(k9_relat_1(X28,k10_relat_1(X28,X27)),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.19/0.38  fof(c_0_34, plain, ![X14, X15, X16]:(~v1_relat_1(X16)|(~r1_tarski(X14,X15)|r1_tarski(k9_relat_1(X16,X14),k9_relat_1(X16,X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,X1))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_26]), c_0_13])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(rw,[status(thm)],[c_0_32, c_0_20])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~r1_tarski(esk5_0,k1_relat_1(k5_relat_1(esk3_0,esk4_0)))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_38, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.38  cnf(c_0_39, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_40, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))|~r1_tarski(esk5_0,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_37, c_0_20])).
% 0.19/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_13])])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0)))|~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_31])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk5_0),k9_relat_1(esk3_0,k10_relat_1(esk3_0,k1_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_45, c_0_13])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,esk5_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_41])])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 51
% 0.19/0.38  # Proof object clause steps            : 34
% 0.19/0.38  # Proof object formula steps           : 17
% 0.19/0.38  # Proof object conjectures             : 27
% 0.19/0.38  # Proof object clause conjectures      : 24
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 15
% 0.19/0.38  # Proof object initial formulas used   : 8
% 0.19/0.38  # Proof object generating inferences   : 13
% 0.19/0.38  # Proof object simplifying inferences  : 17
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 8
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 21
% 0.19/0.38  # Processed clauses                    : 399
% 0.19/0.38  # ...of these trivial                  : 4
% 0.19/0.38  # ...subsumed                          : 30
% 0.19/0.38  # ...remaining for further processing  : 365
% 0.19/0.38  # Other redundant clauses eliminated   : 3
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 78
% 0.19/0.38  # Generated clauses                    : 2082
% 0.19/0.38  # ...of the previous two non-trivial   : 1989
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 2073
% 0.19/0.38  # Factorizations                       : 4
% 0.19/0.38  # Equation resolutions                 : 3
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 260
% 0.19/0.38  #    Positive orientable unit clauses  : 86
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 173
% 0.19/0.38  # Current number of unprocessed clauses: 1610
% 0.19/0.38  # ...number of literals in the above   : 3203
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 102
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 3906
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 2935
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 33
% 0.19/0.38  # Unit Clause-clause subsumption calls : 155
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 89
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 47674
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
