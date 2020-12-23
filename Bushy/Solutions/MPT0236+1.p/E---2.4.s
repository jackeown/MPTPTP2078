%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t31_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:05 EDT 2019

% Result     : Theorem 49.03s
% Output     : CNFRefutation 49.03s
% Verified   : 
% Statistics : Number of formulae       :   54 (1434 expanded)
%              Number of clauses        :   40 ( 775 expanded)
%              Number of leaves         :    7 ( 371 expanded)
%              Depth                    :   17
%              Number of atoms          :  151 (5219 expanded)
%              Number of equality atoms :   56 (1218 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t31_zfmisc_1.p',t7_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t31_zfmisc_1.p',d4_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t31_zfmisc_1.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t31_zfmisc_1.p',d10_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t31_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t31_zfmisc_1.p',d1_tarski)).

fof(t31_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t31_zfmisc_1.p',t31_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_8,plain,(
    ! [X23,X24,X25,X27,X28,X29,X30,X32] :
      ( ( r2_hidden(X25,esk4_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k3_tarski(X23) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k3_tarski(X23) )
      & ( ~ r2_hidden(X27,X28)
        | ~ r2_hidden(X28,X23)
        | r2_hidden(X27,X24)
        | X24 != k3_tarski(X23) )
      & ( ~ r2_hidden(esk5_2(X29,X30),X30)
        | ~ r2_hidden(esk5_2(X29,X30),X32)
        | ~ r2_hidden(X32,X29)
        | X30 = k3_tarski(X29) )
      & ( r2_hidden(esk5_2(X29,X30),esk6_2(X29,X30))
        | r2_hidden(esk5_2(X29,X30),X30)
        | X30 = k3_tarski(X29) )
      & ( r2_hidden(esk6_2(X29,X30),X29)
        | r2_hidden(esk5_2(X29,X30),X30)
        | X30 = k3_tarski(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r1_tarski(X17,X18)
        | ~ r2_hidden(X19,X17)
        | r2_hidden(X19,X18) )
      & ( r2_hidden(esk3_2(X20,X21),X20)
        | r1_tarski(X20,X21) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X21)
        | r1_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( X1 != k3_tarski(X2)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_13])).

cnf(c_0_17,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_18,plain,
    ( X1 != k3_tarski(k3_tarski(X2))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(o_0_0_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_tarski(k3_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( X1 = o_0_0_xboole_0
    | ~ r1_tarski(X1,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_24,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(X2)))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_25,plain,
    ( k3_tarski(X1) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(X1)))) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_28,plain,
    ( k3_tarski(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_29,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(k3_tarski(X2))))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_10])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_28]),c_0_17])])).

cnf(c_0_33,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r2_hidden(esk5_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(X1))))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(esk5_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk5_2(o_0_0_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28])).

cnf(c_0_39,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(X1)))) != k1_tarski(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk6_2(X2,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_33])).

cnf(c_0_41,plain,
    ( esk5_2(o_0_0_xboole_0,k1_tarski(X1)) = X1
    | k1_tarski(X1) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( k1_tarski(X1) != o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_17])])).

cnf(c_0_43,plain,
    ( esk5_2(o_0_0_xboole_0,X1) = k3_tarski(X1)
    | X1 = o_0_0_xboole_0
    | r2_hidden(esk6_2(X1,esk5_2(o_0_0_xboole_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_44,plain,
    ( esk5_2(o_0_0_xboole_0,k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t31_zfmisc_1])).

cnf(c_0_46,plain,
    ( r2_hidden(esk5_2(X1,X2),esk6_2(X1,X2))
    | r2_hidden(esk5_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,plain,
    ( esk6_2(k1_tarski(X1),X1) = X1
    | k3_tarski(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_43]),c_0_44]),c_0_44]),c_0_42])).

fof(c_0_48,negated_conjecture,(
    k3_tarski(k1_tarski(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_49,plain,
    ( k3_tarski(k1_tarski(X1)) = X1
    | r2_hidden(esk5_2(k1_tarski(X1),X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( k3_tarski(k1_tarski(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_49]),c_0_50])]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
