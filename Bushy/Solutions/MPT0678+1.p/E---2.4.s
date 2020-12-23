%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t122_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 186 expanded)
%              Number of clauses        :   39 (  79 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 574 expanded)
%              Number of equality atoms :   62 ( 174 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',t6_boole)).

fof(t122_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2,X3] : k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',t122_funct_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',t2_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',dt_o_0_0_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',d7_xboole_0)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',t149_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',commutativity_k3_xboole_0)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',t117_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',d8_funct_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',t17_zfmisc_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',d16_relat_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',fc2_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t122_funct_1.p',idempotence_k3_xboole_0)).

fof(c_0_13,plain,(
    ! [X41] :
      ( ~ v1_xboole_0(X41)
      | X41 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ! [X2,X3] : k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t122_funct_1])).

fof(c_0_15,plain,(
    ! [X38] : k3_xboole_0(X38,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | k3_xboole_0(X13,X14) = k1_xboole_0 )
      & ( k3_xboole_0(X13,X14) != k1_xboole_0
        | r1_xboole_0(X13,X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_19,negated_conjecture,(
    ! [X5,X6] :
      ( v1_relat_1(esk1_0)
      & v1_funct_1(esk1_0)
      & k9_relat_1(esk1_0,k3_xboole_0(X5,X6)) = k3_xboole_0(k9_relat_1(esk1_0,X5),k9_relat_1(esk1_0,X6))
      & ~ v2_funct_1(esk1_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_22,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k9_relat_1(X33,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

fof(c_0_23,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ r2_hidden(X31,k1_relat_1(X32))
      | k11_relat_1(X32,X31) = k1_tarski(k1_funct_1(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v2_funct_1(X15)
        | ~ r2_hidden(X16,k1_relat_1(X15))
        | ~ r2_hidden(X17,k1_relat_1(X15))
        | k1_funct_1(X15,X16) != k1_funct_1(X15,X17)
        | X16 = X17
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk2_1(X15),k1_relat_1(X15))
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk3_1(X15),k1_relat_1(X15))
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k1_funct_1(X15,esk2_1(X15)) = k1_funct_1(X15,esk3_1(X15))
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk2_1(X15) != esk3_1(X15)
        | v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X34,X35] :
      ( X34 = X35
      | r1_xboole_0(k1_tarski(X34),k1_tarski(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

cnf(c_0_28,negated_conjecture,
    ( k9_relat_1(esk1_0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_30,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | k11_relat_1(X11,X12) = k9_relat_1(X11,k1_tarski(X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_33,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = o_0_0_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_36,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,o_0_0_xboole_0)) = k9_relat_1(esk1_0,o_0_0_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( k9_relat_1(X1,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21]),c_0_21])).

cnf(c_0_39,plain,
    ( k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k11_relat_1(X1,esk3_1(X1)) = k1_tarski(k1_funct_1(X1,esk3_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = o_0_0_xboole_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k9_relat_1(esk1_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_45,plain,
    ( k1_tarski(k1_funct_1(X1,esk3_1(X1))) = k9_relat_1(X1,k1_tarski(esk3_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( k1_funct_1(X1,esk2_1(X1)) = k1_funct_1(X1,esk3_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(k9_relat_1(esk1_0,k1_tarski(X1)),k9_relat_1(esk1_0,k1_tarski(X2))) = o_0_0_xboole_0
    | X1 = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( k9_relat_1(X1,k1_tarski(esk3_1(X1))) = k1_tarski(k1_funct_1(X1,esk2_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,plain,
    ( v2_funct_1(X1)
    | esk2_1(X1) != esk3_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(k1_tarski(k1_funct_1(esk1_0,esk2_1(esk1_0))),k9_relat_1(esk1_0,k1_tarski(X1))) = o_0_0_xboole_0
    | esk3_1(esk1_0) = X1 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_40])]),c_0_50])).

fof(c_0_54,plain,(
    ! [X46] : ~ v1_xboole_0(k1_tarski(X46)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_55,plain,
    ( k11_relat_1(X1,esk2_1(X1)) = k1_tarski(k1_funct_1(X1,esk2_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(k1_tarski(k1_funct_1(esk1_0,esk2_1(esk1_0))),k9_relat_1(esk1_0,k1_tarski(X1))) = o_0_0_xboole_0
    | X1 != esk2_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_49]),c_0_40])]),c_0_50])).

fof(c_0_57,plain,(
    ! [X22] : k3_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_58,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( k1_tarski(k1_funct_1(X1,esk2_1(X1))) = k9_relat_1(X1,k1_tarski(esk2_1(X1)))
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(k9_relat_1(esk1_0,k1_tarski(esk2_1(esk1_0))),k1_tarski(k1_funct_1(esk1_0,esk2_1(esk1_0)))) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_56]),c_0_31])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( v2_funct_1(X1)
    | ~ v1_xboole_0(k9_relat_1(X1,k1_tarski(esk2_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k9_relat_1(esk1_0,k1_tarski(esk2_1(esk1_0))) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_61]),c_0_49]),c_0_40])]),c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_17]),c_0_49]),c_0_40])]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
