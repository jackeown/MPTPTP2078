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
% DateTime   : Thu Dec  3 11:00:49 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 187 expanded)
%              Number of clauses        :   41 (  84 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 571 expanded)
%              Number of equality atoms :   50 ( 135 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t73_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k4_tarski(X3,X3),X2) )
       => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t30_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,k3_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(c_0_15,plain,(
    ! [X25,X26,X27,X28] :
      ( ( k3_relat_1(X26) = X25
        | X26 != k1_wellord2(X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X27,X28),X26)
        | r1_tarski(X27,X28)
        | ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X28,X25)
        | X26 != k1_wellord2(X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(X27,X28)
        | r2_hidden(k4_tarski(X27,X28),X26)
        | ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X28,X25)
        | X26 != k1_wellord2(X25)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(esk2_2(X25,X26),X25)
        | k3_relat_1(X26) != X25
        | X26 = k1_wellord2(X25)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(esk3_2(X25,X26),X25)
        | k3_relat_1(X26) != X25
        | X26 = k1_wellord2(X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X25,X26),esk3_2(X25,X26)),X26)
        | ~ r1_tarski(esk2_2(X25,X26),esk3_2(X25,X26))
        | k3_relat_1(X26) != X25
        | X26 = k1_wellord2(X25)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk2_2(X25,X26),esk3_2(X25,X26)),X26)
        | r1_tarski(esk2_2(X25,X26),esk3_2(X25,X26))
        | k3_relat_1(X26) != X25
        | X26 = k1_wellord2(X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_16,plain,(
    ! [X31] : v1_relat_1(k1_wellord2(X31)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_17,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k3_relat_1(X9) = k2_xboole_0(k1_relat_1(X9),k2_relat_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_18,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_21,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])])).

fof(c_0_23,plain,(
    ! [X16,X17] :
      ( ( r2_hidden(esk1_2(X16,X17),X16)
        | r1_tarski(k6_relat_1(X16),X17)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X16,X17),esk1_2(X16,X17)),X17)
        | r1_tarski(k6_relat_1(X16),X17)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_relat_1])])])])).

fof(c_0_24,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_tarski(k1_relat_1(X20),X19)
      | k7_relat_1(X20,X19) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_22])).

fof(c_0_27,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | k2_wellord1(X24,k3_relat_1(X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_wellord1])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k2_wellord1(X23,X22) = k8_relat_1(X22,k7_relat_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

cnf(c_0_32,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_relat_1(k1_wellord2(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k2_wellord1(X1,k3_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_19])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,k1_wellord2(X2)),X1)
    | r1_tarski(k6_relat_1(X1),k1_wellord2(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | r1_tarski(k2_relat_1(k8_relat_1(X10,X11)),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

cnf(c_0_39,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k7_relat_1(k1_wellord2(X1),X1) = k1_wellord2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19])])).

cnf(c_0_41,plain,
    ( k2_wellord1(k1_wellord2(X1),X1) = k1_wellord2(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_22])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,k1_wellord2(X3))),k1_wellord2(X2))
    | r1_tarski(k6_relat_1(X2),k1_wellord2(X3))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,esk1_2(X2,k1_wellord2(X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k8_relat_1(X1,k1_wellord2(X1)) = k1_wellord2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_19])])).

fof(c_0_46,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(k1_relat_1(X13),k1_relat_1(X14))
        | ~ r1_tarski(X13,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r1_tarski(k2_relat_1(X13),k2_relat_1(X14))
        | ~ r1_tarski(X13,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_47,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X1,X2)),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,k1_wellord2(X2)),esk1_2(X1,k1_wellord2(X2))),k1_wellord2(X1))
    | r1_tarski(k6_relat_1(X1),k1_wellord2(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_36])).

fof(c_0_49,plain,(
    ! [X15] :
      ( k1_relat_1(k6_relat_1(X15)) = X15
      & k2_relat_1(k6_relat_1(X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_50,plain,(
    ! [X21] :
      ( v1_relat_1(k6_relat_1(X21))
      & v2_funct_1(k6_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_19])])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( r1_tarski(k6_relat_1(X1),k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_19])])).

cnf(c_0_55,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_59,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

fof(c_0_60,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(X12,k2_zfmisc_1(k1_relat_1(X12),k2_relat_1(X12))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_61,plain,
    ( k2_relat_1(k1_wellord2(X1)) = X1
    | ~ r1_tarski(X1,k2_relat_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k2_relat_1(k1_wellord2(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_19]),c_0_56])])).

cnf(c_0_63,plain,
    ( k1_relat_1(k1_wellord2(X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_33])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k1_relat_1(k1_wellord2(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_58]),c_0_19]),c_0_56])])).

fof(c_0_65,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk4_0),k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( k2_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_68,plain,
    ( k1_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk4_0),k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_19])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S015I
% 0.21/0.40  # and selection function PSelectOptimalLit.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.028 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.21/0.40  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.21/0.40  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.21/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.40  fof(t73_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(![X3]:(r2_hidden(X3,X1)=>r2_hidden(k4_tarski(X3,X3),X2))=>r1_tarski(k6_relat_1(X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 0.21/0.40  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.21/0.40  fof(t30_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>k2_wellord1(X1,k3_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 0.21/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.40  fof(t18_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k8_relat_1(X1,k7_relat_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 0.21/0.40  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.21/0.40  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.21/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.40  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.21/0.40  fof(t33_wellord2, conjecture, ![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 0.21/0.40  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.21/0.40  fof(c_0_15, plain, ![X25, X26, X27, X28]:(((k3_relat_1(X26)=X25|X26!=k1_wellord2(X25)|~v1_relat_1(X26))&((~r2_hidden(k4_tarski(X27,X28),X26)|r1_tarski(X27,X28)|(~r2_hidden(X27,X25)|~r2_hidden(X28,X25))|X26!=k1_wellord2(X25)|~v1_relat_1(X26))&(~r1_tarski(X27,X28)|r2_hidden(k4_tarski(X27,X28),X26)|(~r2_hidden(X27,X25)|~r2_hidden(X28,X25))|X26!=k1_wellord2(X25)|~v1_relat_1(X26))))&(((r2_hidden(esk2_2(X25,X26),X25)|k3_relat_1(X26)!=X25|X26=k1_wellord2(X25)|~v1_relat_1(X26))&(r2_hidden(esk3_2(X25,X26),X25)|k3_relat_1(X26)!=X25|X26=k1_wellord2(X25)|~v1_relat_1(X26)))&((~r2_hidden(k4_tarski(esk2_2(X25,X26),esk3_2(X25,X26)),X26)|~r1_tarski(esk2_2(X25,X26),esk3_2(X25,X26))|k3_relat_1(X26)!=X25|X26=k1_wellord2(X25)|~v1_relat_1(X26))&(r2_hidden(k4_tarski(esk2_2(X25,X26),esk3_2(X25,X26)),X26)|r1_tarski(esk2_2(X25,X26),esk3_2(X25,X26))|k3_relat_1(X26)!=X25|X26=k1_wellord2(X25)|~v1_relat_1(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.21/0.40  fof(c_0_16, plain, ![X31]:v1_relat_1(k1_wellord2(X31)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.21/0.40  fof(c_0_17, plain, ![X9]:(~v1_relat_1(X9)|k3_relat_1(X9)=k2_xboole_0(k1_relat_1(X9),k2_relat_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.21/0.40  cnf(c_0_18, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_19, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  fof(c_0_20, plain, ![X7, X8]:r1_tarski(X7,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.40  cnf(c_0_21, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_22, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_19])])).
% 0.21/0.40  fof(c_0_23, plain, ![X16, X17]:((r2_hidden(esk1_2(X16,X17),X16)|r1_tarski(k6_relat_1(X16),X17)|~v1_relat_1(X17))&(~r2_hidden(k4_tarski(esk1_2(X16,X17),esk1_2(X16,X17)),X17)|r1_tarski(k6_relat_1(X16),X17)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_relat_1])])])])).
% 0.21/0.40  fof(c_0_24, plain, ![X19, X20]:(~v1_relat_1(X20)|(~r1_tarski(k1_relat_1(X20),X19)|k7_relat_1(X20,X19)=X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.21/0.40  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_26, plain, (k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_22])).
% 0.21/0.40  fof(c_0_27, plain, ![X24]:(~v1_relat_1(X24)|k2_wellord1(X24,k3_relat_1(X24))=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_wellord1])])).
% 0.21/0.40  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  fof(c_0_30, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.40  fof(c_0_31, plain, ![X22, X23]:(~v1_relat_1(X23)|k2_wellord1(X23,X22)=k8_relat_1(X22,k7_relat_1(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).
% 0.21/0.40  cnf(c_0_32, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.40  cnf(c_0_33, plain, (r1_tarski(k1_relat_1(k1_wellord2(X1)),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.40  cnf(c_0_34, plain, (k2_wellord1(X1,k3_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.40  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_19])])).
% 0.21/0.40  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,k1_wellord2(X2)),X1)|r1_tarski(k6_relat_1(X1),k1_wellord2(X2))), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 0.21/0.40  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  fof(c_0_38, plain, ![X10, X11]:(~v1_relat_1(X11)|r1_tarski(k2_relat_1(k8_relat_1(X10,X11)),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.21/0.40  cnf(c_0_39, plain, (k2_wellord1(X1,X2)=k8_relat_1(X2,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.40  cnf(c_0_40, plain, (k7_relat_1(k1_wellord2(X1),X1)=k1_wellord2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_19])])).
% 0.21/0.40  cnf(c_0_41, plain, (k2_wellord1(k1_wellord2(X1),X1)=k1_wellord2(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_22])).
% 0.21/0.40  cnf(c_0_42, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,k1_wellord2(X3))),k1_wellord2(X2))|r1_tarski(k6_relat_1(X2),k1_wellord2(X3))|~r2_hidden(X1,X2)|~r1_tarski(X1,esk1_2(X2,k1_wellord2(X3)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.40  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.21/0.40  cnf(c_0_44, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.40  cnf(c_0_45, plain, (k8_relat_1(X1,k1_wellord2(X1))=k1_wellord2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_19])])).
% 0.21/0.40  fof(c_0_46, plain, ![X13, X14]:((r1_tarski(k1_relat_1(X13),k1_relat_1(X14))|~r1_tarski(X13,X14)|~v1_relat_1(X14)|~v1_relat_1(X13))&(r1_tarski(k2_relat_1(X13),k2_relat_1(X14))|~r1_tarski(X13,X14)|~v1_relat_1(X14)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.21/0.40  cnf(c_0_47, plain, (r1_tarski(k6_relat_1(X1),X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X1,X2)),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.40  cnf(c_0_48, plain, (r2_hidden(k4_tarski(esk1_2(X1,k1_wellord2(X2)),esk1_2(X1,k1_wellord2(X2))),k1_wellord2(X1))|r1_tarski(k6_relat_1(X1),k1_wellord2(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_36])).
% 0.21/0.40  fof(c_0_49, plain, ![X15]:(k1_relat_1(k6_relat_1(X15))=X15&k2_relat_1(k6_relat_1(X15))=X15), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.40  fof(c_0_50, plain, ![X21]:(v1_relat_1(k6_relat_1(X21))&v2_funct_1(k6_relat_1(X21))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.21/0.40  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_52, plain, (r1_tarski(k2_relat_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_19])])).
% 0.21/0.40  cnf(c_0_53, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.40  cnf(c_0_54, plain, (r1_tarski(k6_relat_1(X1),k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_19])])).
% 0.21/0.40  cnf(c_0_55, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.40  cnf(c_0_56, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.40  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.40  cnf(c_0_58, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.40  fof(c_0_59, negated_conjecture, ~(![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(assume_negation,[status(cth)],[t33_wellord2])).
% 0.21/0.40  fof(c_0_60, plain, ![X12]:(~v1_relat_1(X12)|r1_tarski(X12,k2_zfmisc_1(k1_relat_1(X12),k2_relat_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.21/0.40  cnf(c_0_61, plain, (k2_relat_1(k1_wellord2(X1))=X1|~r1_tarski(X1,k2_relat_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.40  cnf(c_0_62, plain, (r1_tarski(X1,k2_relat_1(k1_wellord2(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_19]), c_0_56])])).
% 0.21/0.40  cnf(c_0_63, plain, (k1_relat_1(k1_wellord2(X1))=X1|~r1_tarski(X1,k1_relat_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_51, c_0_33])).
% 0.21/0.40  cnf(c_0_64, plain, (r1_tarski(X1,k1_relat_1(k1_wellord2(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_54]), c_0_58]), c_0_19]), c_0_56])])).
% 0.21/0.40  fof(c_0_65, negated_conjecture, ~r1_tarski(k1_wellord2(esk4_0),k2_zfmisc_1(esk4_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).
% 0.21/0.40  cnf(c_0_66, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.40  cnf(c_0_67, plain, (k2_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.21/0.40  cnf(c_0_68, plain, (k1_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.21/0.40  cnf(c_0_69, negated_conjecture, (~r1_tarski(k1_wellord2(esk4_0),k2_zfmisc_1(esk4_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.40  cnf(c_0_70, plain, (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_19])])).
% 0.21/0.40  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 72
% 0.21/0.40  # Proof object clause steps            : 41
% 0.21/0.40  # Proof object formula steps           : 31
% 0.21/0.40  # Proof object conjectures             : 5
% 0.21/0.40  # Proof object clause conjectures      : 2
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 20
% 0.21/0.40  # Proof object initial formulas used   : 15
% 0.21/0.40  # Proof object generating inferences   : 15
% 0.21/0.40  # Proof object simplifying inferences  : 36
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 15
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 27
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 27
% 0.21/0.40  # Processed clauses                    : 376
% 0.21/0.40  # ...of these trivial                  : 44
% 0.21/0.40  # ...subsumed                          : 114
% 0.21/0.40  # ...remaining for further processing  : 218
% 0.21/0.40  # Other redundant clauses eliminated   : 9
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 78
% 0.21/0.40  # Generated clauses                    : 737
% 0.21/0.40  # ...of the previous two non-trivial   : 678
% 0.21/0.40  # Contextual simplify-reflections      : 1
% 0.21/0.40  # Paramodulations                      : 728
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 9
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 105
% 0.21/0.40  #    Positive orientable unit clauses  : 45
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 0
% 0.21/0.40  #    Non-unit-clauses                  : 60
% 0.21/0.40  # Current number of unprocessed clauses: 353
% 0.21/0.40  # ...number of literals in the above   : 772
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 104
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 1972
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 1786
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 113
% 0.21/0.40  # Unit Clause-clause subsumption calls : 159
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 191
% 0.21/0.40  # BW rewrite match successes           : 12
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 17649
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.050 s
% 0.21/0.40  # System time              : 0.005 s
% 0.21/0.40  # Total time               : 0.055 s
% 0.21/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
