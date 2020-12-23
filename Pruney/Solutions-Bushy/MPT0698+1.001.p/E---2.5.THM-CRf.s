%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0698+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 346 expanded)
%              Number of clauses        :   36 ( 123 expanded)
%              Number of leaves         :    8 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 (1402 expanded)
%              Number of equality atoms :   61 ( 193 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t153_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2] : r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ! [X2] : r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t153_funct_1])).

fof(c_0_9,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_funct_1(X17)
        | ~ r2_hidden(X18,k1_relat_1(X17))
        | ~ r2_hidden(X19,k1_relat_1(X17))
        | k1_funct_1(X17,X18) != k1_funct_1(X17,X19)
        | X18 = X19
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk4_1(X17),k1_relat_1(X17))
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk5_1(X17),k1_relat_1(X17))
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_funct_1(X17,esk4_1(X17)) = k1_funct_1(X17,esk5_1(X17))
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk4_1(X17) != esk5_1(X17)
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X31] :
      ( v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & r1_tarski(k10_relat_1(esk6_0,k9_relat_1(esk6_0,X31)),X31)
      & ~ v2_funct_1(esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | k11_relat_1(X5,X6) = k9_relat_1(X5,k1_tarski(X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_12,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ r2_hidden(X22,k1_relat_1(X23))
      | k11_relat_1(X23,X22) = k1_tarski(k1_funct_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk5_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( ~ r1_tarski(X26,k1_tarski(X27))
        | X26 = k1_xboole_0
        | X26 = k1_tarski(X27) )
      & ( X26 != k1_xboole_0
        | r1_tarski(X26,k1_tarski(X27)) )
      & ( X26 != k1_tarski(X27)
        | r1_tarski(X26,k1_tarski(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,k9_relat_1(esk6_0,X1)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_23,plain,
    ( k1_funct_1(X1,esk4_1(X1)) = k1_funct_1(X1,esk5_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_25,plain,(
    ! [X24,X25] :
      ( ( ~ r2_hidden(X24,k2_relat_1(X25))
        | k10_relat_1(X25,k1_tarski(X24)) != k1_xboole_0
        | ~ v1_relat_1(X25) )
      & ( k10_relat_1(X25,k1_tarski(X24)) = k1_xboole_0
        | r2_hidden(X24,k2_relat_1(X25))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_26,plain,(
    ! [X7,X8,X9,X11,X12,X13,X15] :
      ( ( r2_hidden(esk1_3(X7,X8,X9),k1_relat_1(X7))
        | ~ r2_hidden(X9,X8)
        | X8 != k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 = k1_funct_1(X7,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(X12,k1_relat_1(X7))
        | X11 != k1_funct_1(X7,X12)
        | r2_hidden(X11,X8)
        | X8 != k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(esk2_2(X7,X13),X13)
        | ~ r2_hidden(X15,k1_relat_1(X7))
        | esk2_2(X7,X13) != k1_funct_1(X7,X15)
        | X13 = k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(esk3_2(X7,X13),k1_relat_1(X7))
        | r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( esk2_2(X7,X13) = k1_funct_1(X7,esk3_2(X7,X13))
        | r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k2_relat_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,k11_relat_1(esk6_0,X1)),k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_15])])).

cnf(c_0_29,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk6_0,esk5_1(esk6_0))) = k11_relat_1(esk6_0,esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_1(esk6_0)) = k1_funct_1(esk6_0,esk4_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk6_0,esk4_1(esk6_0))) = k11_relat_1(esk6_0,esk4_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_14]),c_0_15])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk6_0,k11_relat_1(esk6_0,X1)) = k1_tarski(X1)
    | k10_relat_1(esk6_0,k11_relat_1(esk6_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k11_relat_1(esk6_0,esk5_1(esk6_0)) = k11_relat_1(esk6_0,esk4_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k10_relat_1(X1,k11_relat_1(esk6_0,esk4_1(esk6_0))) != k1_xboole_0
    | ~ r2_hidden(k1_funct_1(esk6_0,esk4_1(esk6_0)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk6_0,k11_relat_1(esk6_0,X1)) = k1_xboole_0
    | k1_tarski(X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk6_0,k11_relat_1(esk6_0,esk4_1(esk6_0))),k1_tarski(esk5_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(esk6_0,k11_relat_1(esk6_0,esk4_1(esk6_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_15]),c_0_24]),c_0_14])])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk6_0,k11_relat_1(esk6_0,esk4_1(esk6_0))) = k1_xboole_0
    | k1_tarski(esk5_1(esk6_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_35])).

fof(c_0_42,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(k1_tarski(X28),k1_tarski(X29))
      | X28 = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk6_0,k11_relat_1(esk6_0,esk4_1(esk6_0))) = k1_tarski(esk5_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_39]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k1_tarski(esk5_1(esk6_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k1_tarski(esk5_1(esk6_0)) = k1_tarski(esk4_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_43]),c_0_44])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( X1 = esk5_1(esk6_0)
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(esk4_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_50,plain,
    ( v2_funct_1(X1)
    | esk4_1(X1) != esk5_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( esk5_1(esk6_0) = esk4_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_14]),c_0_15])]),c_0_16]),
    [proof]).

%------------------------------------------------------------------------------
