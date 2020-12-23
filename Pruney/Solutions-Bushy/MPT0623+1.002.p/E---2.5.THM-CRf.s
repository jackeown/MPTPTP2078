%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0623+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:55 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 117 expanded)
%              Number of clauses        :   40 (  52 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 ( 418 expanded)
%              Number of equality atoms :   47 ( 120 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(s3_funct_1__e1_27_1__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X2
      & ! [X4] :
          ( r2_hidden(X4,X2)
         => k1_funct_1(X3,X4) = o_1_0_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(fc11_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_o_1_0_funct_1,axiom,(
    ! [X1] : m1_subset_1(o_1_0_funct_1(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_13,plain,(
    ! [X13,X14,X15,X17,X18,X19,X21] :
      ( ( r2_hidden(esk2_3(X13,X14,X15),k1_relat_1(X13))
        | ~ r2_hidden(X15,X14)
        | X14 != k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X15 = k1_funct_1(X13,esk2_3(X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X18,k1_relat_1(X13))
        | X17 != k1_funct_1(X13,X18)
        | r2_hidden(X17,X14)
        | X14 != k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(esk3_2(X13,X19),X19)
        | ~ r2_hidden(X21,k1_relat_1(X13))
        | esk3_2(X13,X19) != k1_funct_1(X13,X21)
        | X19 = k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk4_2(X13,X19),k1_relat_1(X13))
        | r2_hidden(esk3_2(X13,X19),X19)
        | X19 = k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( esk3_2(X13,X19) = k1_funct_1(X13,esk4_2(X13,X19))
        | r2_hidden(esk3_2(X13,X19),X19)
        | X19 = k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X29] :
      ( v1_relat_1(esk5_2(X26,X27))
      & v1_funct_1(esk5_2(X26,X27))
      & k1_relat_1(esk5_2(X26,X27)) = X27
      & ( ~ r2_hidden(X29,X27)
        | k1_funct_1(esk5_2(X26,X27),X29) = o_1_0_funct_1(X26) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e1_27_1__funct_1])])])])).

cnf(c_0_15,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_funct_1(esk5_2(X3,X2),X1) = o_1_0_funct_1(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X1 = o_1_0_funct_1(X2)
    | ~ r2_hidden(esk2_3(esk5_2(X2,X3),k2_relat_1(esk5_2(X2,X3)),X1),X3)
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),X3)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_31,plain,
    ( X1 = o_1_0_funct_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_20]),c_0_21])])).

fof(c_0_32,plain,(
    ! [X33] :
      ( ~ v1_xboole_0(X33)
      | X33 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_33,plain,(
    ! [X25] :
      ( ~ v1_xboole_0(X25)
      | v1_xboole_0(k2_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).

fof(c_0_34,negated_conjecture,(
    ! [X36] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | esk7_0 != k1_relat_1(X36)
        | ~ r1_tarski(k2_relat_1(X36),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).

cnf(c_0_35,plain,
    ( esk1_2(k2_relat_1(esk5_2(X1,X2)),X3) = o_1_0_funct_1(X1)
    | r1_tarski(k2_relat_1(esk5_2(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

fof(c_0_36,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_37,plain,(
    ! [X23] : m1_subset_1(o_1_0_funct_1(X23),X23) ),
    inference(variable_rename,[status(thm)],[dt_o_1_0_funct_1])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X32] : r1_tarski(k1_xboole_0,X32) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_41,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | v1_funct_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_42,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_43,plain,(
    ! [X24] :
      ( ~ v1_xboole_0(X24)
      | v1_xboole_0(k1_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,X2)),X3)
    | ~ r2_hidden(o_1_0_funct_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_35])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( m1_subset_1(o_1_0_funct_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(o_1_0_funct_1(X1),esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28]),c_0_20]),c_0_21])])])).

cnf(c_0_55,plain,
    ( r2_hidden(o_1_0_funct_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(X1) != esk7_0
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_48]),c_0_49])]),c_0_50]),c_0_51])).

cnf(c_0_57,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_52])).

cnf(c_0_58,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),c_0_64]),
    [proof]).

%------------------------------------------------------------------------------
