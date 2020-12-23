%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:54 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 137 expanded)
%              Number of clauses        :   32 (  66 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  166 ( 533 expanded)
%              Number of equality atoms :   37 (  87 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(t1_mcart_1,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_7,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_8,plain,(
    ! [X12,X13,X15] :
      ( ( r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,esk2_2(X12,X13))
        | ~ r2_hidden(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t1_mcart_1])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,negated_conjecture,(
    ! [X31] :
      ( esk6_0 != k1_xboole_0
      & ( ~ r2_hidden(X31,esk6_0)
        | ~ r1_xboole_0(X31,esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,esk2_2(X2,X3))
    | ~ r2_hidden(esk1_2(X1,esk2_2(X2,X3)),X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,esk2_2(X2,X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r1_xboole_0(esk2_2(X1,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r1_xboole_0(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X17,X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( r2_hidden(esk3_4(X17,X18,X19,X20),k1_relat_1(X17))
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk3_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X20 = k1_funct_1(X17,esk3_4(X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X23,k1_relat_1(X17))
        | ~ r2_hidden(X23,X18)
        | X22 != k1_funct_1(X17,X23)
        | r2_hidden(X22,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(esk4_3(X17,X24,X25),X25)
        | ~ r2_hidden(X27,k1_relat_1(X17))
        | ~ r2_hidden(X27,X24)
        | esk4_3(X17,X24,X25) != k1_funct_1(X17,X27)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk5_3(X17,X24,X25),k1_relat_1(X17))
        | r2_hidden(esk4_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk5_3(X17,X24,X25),X24)
        | r2_hidden(esk4_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk4_3(X17,X24,X25) = k1_funct_1(X17,esk5_3(X17,X24,X25))
        | r2_hidden(esk4_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_24,plain,(
    ! [X29] :
      ( v1_relat_1(k6_relat_1(X29))
      & v1_funct_1(k6_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X16] : k9_relat_1(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_28,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_30,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( X1 != k9_relat_1(X2,esk6_0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X4,X5)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X4 != k1_funct_1(X2,X1)
    | X5 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_37,plain,
    ( X1 != k1_funct_1(k1_xboole_0,X2)
    | X3 != k1_xboole_0
    | ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_33]),c_0_34])]),c_0_36])).

cnf(c_0_38,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(X2,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_39,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(esk2_2(X2,k1_relat_1(k1_xboole_0)),X3)
    | ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_40,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_41,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)
    | X3 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:30:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.15/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.37  #
% 0.15/0.37  # Preprocessing time       : 0.017 s
% 0.15/0.37  # Presaturation interreduction done
% 0.15/0.37  
% 0.15/0.37  # Proof found!
% 0.15/0.37  # SZS status Theorem
% 0.15/0.37  # SZS output start CNFRefutation
% 0.15/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.15/0.37  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.15/0.37  fof(t1_mcart_1, conjecture, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.15/0.37  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.15/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.15/0.37  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 0.15/0.37  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.15/0.37  fof(c_0_7, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.15/0.37  fof(c_0_8, plain, ![X12, X13, X15]:((r2_hidden(esk2_2(X12,X13),X13)|~r2_hidden(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,esk2_2(X12,X13))|~r2_hidden(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.15/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1)))))), inference(assume_negation,[status(cth)],[t1_mcart_1])).
% 0.15/0.37  cnf(c_0_10, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.37  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.37  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.37  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.37  fof(c_0_14, negated_conjecture, ![X31]:(esk6_0!=k1_xboole_0&(~r2_hidden(X31,esk6_0)|~r1_xboole_0(X31,esk6_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.15/0.37  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.15/0.37  cnf(c_0_16, plain, (r1_xboole_0(X1,esk2_2(X2,X3))|~r2_hidden(esk1_2(X1,esk2_2(X2,X3)),X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.15/0.37  cnf(c_0_17, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r1_xboole_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.37  cnf(c_0_18, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.37  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_13])).
% 0.15/0.37  cnf(c_0_20, plain, (r1_xboole_0(X1,esk2_2(X2,X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_16, c_0_11])).
% 0.15/0.37  cnf(c_0_21, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r1_xboole_0(esk2_2(X1,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.15/0.37  cnf(c_0_22, plain, (r1_xboole_0(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.15/0.37  fof(c_0_23, plain, ![X17, X18, X19, X20, X22, X23, X24, X25, X27]:(((((r2_hidden(esk3_4(X17,X18,X19,X20),k1_relat_1(X17))|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(r2_hidden(esk3_4(X17,X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(X20=k1_funct_1(X17,esk3_4(X17,X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(X23,k1_relat_1(X17))|~r2_hidden(X23,X18)|X22!=k1_funct_1(X17,X23)|r2_hidden(X22,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&((~r2_hidden(esk4_3(X17,X24,X25),X25)|(~r2_hidden(X27,k1_relat_1(X17))|~r2_hidden(X27,X24)|esk4_3(X17,X24,X25)!=k1_funct_1(X17,X27))|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(((r2_hidden(esk5_3(X17,X24,X25),k1_relat_1(X17))|r2_hidden(esk4_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(r2_hidden(esk5_3(X17,X24,X25),X24)|r2_hidden(esk4_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(esk4_3(X17,X24,X25)=k1_funct_1(X17,esk5_3(X17,X24,X25))|r2_hidden(esk4_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.15/0.37  fof(c_0_24, plain, ![X29]:(v1_relat_1(k6_relat_1(X29))&v1_funct_1(k6_relat_1(X29))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.15/0.37  cnf(c_0_25, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.15/0.37  cnf(c_0_26, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.37  fof(c_0_27, plain, ![X16]:k9_relat_1(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.15/0.37  cnf(c_0_28, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.37  cnf(c_0_29, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.15/0.37  cnf(c_0_30, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.37  cnf(c_0_31, negated_conjecture, (X1!=k9_relat_1(X2,esk6_0)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.37  cnf(c_0_32, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.37  cnf(c_0_33, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.15/0.37  cnf(c_0_34, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.15/0.37  cnf(c_0_35, plain, (r2_hidden(X4,X5)|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X4!=k1_funct_1(X2,X1)|X5!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.37  cnf(c_0_36, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.15/0.37  cnf(c_0_37, plain, (X1!=k1_funct_1(k1_xboole_0,X2)|X3!=k1_xboole_0|~r2_hidden(X2,k1_relat_1(k1_xboole_0))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_33]), c_0_34])]), c_0_36])).
% 0.15/0.37  cnf(c_0_38, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_relat_1(k1_xboole_0))|~r2_hidden(X2,X3)), inference(er,[status(thm)],[c_0_37])).
% 0.15/0.37  cnf(c_0_39, plain, (X1!=k1_xboole_0|~r2_hidden(esk2_2(X2,k1_relat_1(k1_xboole_0)),X3)|~r2_hidden(X2,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_38, c_0_18])).
% 0.15/0.37  cnf(c_0_40, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_18])).
% 0.15/0.37  cnf(c_0_41, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.37  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)|X3!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32]), c_0_33]), c_0_34])])).
% 0.15/0.37  cnf(c_0_43, plain, (X1=k1_xboole_0|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)), inference(er,[status(thm)],[c_0_42])).
% 0.15/0.37  cnf(c_0_44, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_43]), c_0_44]), ['proof']).
% 0.15/0.37  # SZS output end CNFRefutation
% 0.15/0.37  # Proof object total steps             : 46
% 0.15/0.37  # Proof object clause steps            : 32
% 0.15/0.37  # Proof object formula steps           : 14
% 0.15/0.37  # Proof object conjectures             : 10
% 0.15/0.37  # Proof object clause conjectures      : 7
% 0.15/0.37  # Proof object formula conjectures     : 3
% 0.15/0.37  # Proof object initial clauses used    : 14
% 0.15/0.37  # Proof object initial formulas used   : 7
% 0.15/0.37  # Proof object generating inferences   : 18
% 0.15/0.37  # Proof object simplifying inferences  : 12
% 0.15/0.37  # Training examples: 0 positive, 0 negative
% 0.15/0.37  # Parsed axioms                        : 7
% 0.15/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.37  # Initial clauses                      : 19
% 0.15/0.37  # Removed in clause preprocessing      : 0
% 0.15/0.37  # Initial clauses in saturation        : 19
% 0.15/0.37  # Processed clauses                    : 145
% 0.15/0.37  # ...of these trivial                  : 7
% 0.15/0.37  # ...subsumed                          : 45
% 0.15/0.37  # ...remaining for further processing  : 93
% 0.15/0.37  # Other redundant clauses eliminated   : 1
% 0.15/0.37  # Clauses deleted for lack of memory   : 0
% 0.15/0.37  # Backward-subsumed                    : 5
% 0.15/0.37  # Backward-rewritten                   : 6
% 0.15/0.37  # Generated clauses                    : 192
% 0.15/0.37  # ...of the previous two non-trivial   : 164
% 0.15/0.37  # Contextual simplify-reflections      : 1
% 0.15/0.37  # Paramodulations                      : 180
% 0.15/0.37  # Factorizations                       : 0
% 0.15/0.37  # Equation resolutions                 : 12
% 0.15/0.37  # Propositional unsat checks           : 0
% 0.15/0.37  #    Propositional check models        : 0
% 0.15/0.37  #    Propositional check unsatisfiable : 0
% 0.15/0.37  #    Propositional clauses             : 0
% 0.15/0.37  #    Propositional clauses after purity: 0
% 0.15/0.37  #    Propositional unsat core size     : 0
% 0.15/0.37  #    Propositional preprocessing time  : 0.000
% 0.15/0.37  #    Propositional encoding time       : 0.000
% 0.15/0.37  #    Propositional solver time         : 0.000
% 0.15/0.37  #    Success case prop preproc time    : 0.000
% 0.15/0.37  #    Success case prop encoding time   : 0.000
% 0.15/0.37  #    Success case prop solver time     : 0.000
% 0.15/0.37  # Current number of processed clauses  : 63
% 0.15/0.37  #    Positive orientable unit clauses  : 12
% 0.15/0.37  #    Positive unorientable unit clauses: 0
% 0.15/0.37  #    Negative unit clauses             : 3
% 0.15/0.37  #    Non-unit-clauses                  : 48
% 0.15/0.37  # Current number of unprocessed clauses: 53
% 0.15/0.37  # ...number of literals in the above   : 268
% 0.15/0.37  # Current number of archived formulas  : 0
% 0.15/0.37  # Current number of archived clauses   : 30
% 0.15/0.37  # Clause-clause subsumption calls (NU) : 1240
% 0.15/0.37  # Rec. Clause-clause subsumption calls : 536
% 0.15/0.37  # Non-unit clause-clause subsumptions  : 42
% 0.15/0.37  # Unit Clause-clause subsumption calls : 41
% 0.15/0.37  # Rewrite failures with RHS unbound    : 0
% 0.15/0.37  # BW rewrite match attempts            : 6
% 0.15/0.37  # BW rewrite match successes           : 6
% 0.15/0.37  # Condensation attempts                : 0
% 0.15/0.37  # Condensation successes               : 0
% 0.15/0.37  # Termbank termtop insertions          : 3746
% 0.15/0.37  
% 0.15/0.37  # -------------------------------------------------
% 0.15/0.37  # User time                : 0.017 s
% 0.15/0.37  # System time              : 0.007 s
% 0.15/0.37  # Total time               : 0.025 s
% 0.15/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
