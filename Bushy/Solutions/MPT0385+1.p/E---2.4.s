%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t3_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   40 (  86 expanded)
%              Number of clauses        :   23 (  39 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 322 expanded)
%              Number of equality atoms :   44 ( 125 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',existence_m1_subset_1)).

fof(t3_setfam_1,conjecture,(
    ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',t3_setfam_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',t6_boole)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',d1_setfam_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',d3_tarski)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t3_setfam_1.p',d4_tarski)).

fof(c_0_8,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_9,plain,(
    ! [X39] : m1_subset_1(esk9_1(X39),X39) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(assume_negation,[status(cth)],[t3_setfam_1])).

fof(c_0_11,plain,(
    ! [X54] :
      ( ~ v1_xboole_0(X54)
      | X54 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_12,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X8,X9,X10,X11,X12,X14,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X10,X9)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X10,X11)
        | X9 != k1_setfam_1(X8)
        | X8 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X8,X9,X12),X8)
        | r2_hidden(X12,X9)
        | X9 != k1_setfam_1(X8)
        | X8 = k1_xboole_0 )
      & ( ~ r2_hidden(X12,esk2_3(X8,X9,X12))
        | r2_hidden(X12,X9)
        | X9 != k1_setfam_1(X8)
        | X8 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X8,X14),X8)
        | ~ r2_hidden(esk3_2(X8,X14),X14)
        | X14 = k1_setfam_1(X8)
        | X8 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X8,X14),esk4_2(X8,X14))
        | ~ r2_hidden(esk3_2(X8,X14),X14)
        | X14 = k1_setfam_1(X8)
        | X8 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X8,X14),X14)
        | ~ r2_hidden(X17,X8)
        | r2_hidden(esk3_2(X8,X14),X17)
        | X14 = k1_setfam_1(X8)
        | X8 = k1_xboole_0 )
      & ( X19 != k1_setfam_1(X18)
        | X19 = k1_xboole_0
        | X18 != k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | X20 = k1_setfam_1(X18)
        | X18 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ r1_tarski(k1_setfam_1(esk1_0),k3_tarski(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X45] : r1_tarski(k1_xboole_0,X45) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk1_0),k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(X23,X22) )
      & ( r2_hidden(esk5_2(X24,X25),X24)
        | r1_tarski(X24,X25) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( r2_hidden(X29,esk6_3(X27,X28,X29))
        | ~ r2_hidden(X29,X28)
        | X28 != k3_tarski(X27) )
      & ( r2_hidden(esk6_3(X27,X28,X29),X27)
        | ~ r2_hidden(X29,X28)
        | X28 != k3_tarski(X27) )
      & ( ~ r2_hidden(X31,X32)
        | ~ r2_hidden(X32,X27)
        | r2_hidden(X31,X28)
        | X28 != k3_tarski(X27) )
      & ( ~ r2_hidden(esk7_2(X33,X34),X34)
        | ~ r2_hidden(esk7_2(X33,X34),X36)
        | ~ r2_hidden(X36,X33)
        | X34 = k3_tarski(X33) )
      & ( r2_hidden(esk7_2(X33,X34),esk8_2(X33,X34))
        | r2_hidden(esk7_2(X33,X34),X34)
        | X34 = k3_tarski(X33) )
      & ( r2_hidden(esk8_2(X33,X34),X33)
        | r2_hidden(esk7_2(X33,X34),X34)
        | X34 = k3_tarski(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk9_1(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r2_hidden(X1,esk9_1(esk1_0))
    | ~ r2_hidden(X1,k1_setfam_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_2(k1_setfam_1(esk1_0),k3_tarski(esk1_0)),k1_setfam_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r2_hidden(esk5_2(k1_setfam_1(esk1_0),k3_tarski(esk1_0)),esk9_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk1_0))
    | ~ r2_hidden(X1,esk9_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_2(k1_setfam_1(esk1_0),k3_tarski(esk1_0)),esk9_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_34]),c_0_23]),c_0_24])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk5_2(k1_setfam_1(esk1_0),k3_tarski(esk1_0)),k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
