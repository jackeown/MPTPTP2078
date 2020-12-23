%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t55_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:18 EDT 2019

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 620 expanded)
%              Number of clauses        :   64 ( 285 expanded)
%              Number of leaves         :   17 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  236 (1645 expanded)
%              Number of equality atoms :   58 ( 303 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',d4_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',fc1_subset_1)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t37_zfmisc_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',d8_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',dt_k7_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t2_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',d5_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t3_boole)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',d1_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t4_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t7_boole)).

fof(t55_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 = k1_tarski(X1)
       => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t55_setfam_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',t37_xboole_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t55_setfam_1.p',involutiveness_k7_setfam_1)).

fof(c_0_17,plain,(
    ! [X25] : m1_subset_1(k2_subset_1(X25),k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_18,plain,(
    ! [X16] : k2_subset_1(X16) = X16 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X38,X39)
      | v1_xboole_0(X39)
      | r2_hidden(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X60] : ~ v1_xboole_0(k1_zfmisc_1(X60)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_23,plain,(
    ! [X43,X44] :
      ( ( ~ r1_tarski(k1_tarski(X43),X44)
        | r2_hidden(X43,X44) )
      & ( ~ r2_hidden(X43,X44)
        | r1_tarski(k1_tarski(X43),X44) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k3_subset_1(X19,X22),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X19))
        | X21 != k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( ~ r2_hidden(k3_subset_1(X19,X22),X20)
        | r2_hidden(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X19))
        | X21 != k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( m1_subset_1(esk4_3(X19,X20,X21),k1_zfmisc_1(X19))
        | X21 = k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( ~ r2_hidden(esk4_3(X19,X20,X21),X21)
        | ~ r2_hidden(k3_subset_1(X19,esk4_3(X19,X20,X21)),X20)
        | X21 = k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( r2_hidden(esk4_3(X19,X20,X21),X21)
        | r2_hidden(k3_subset_1(X19,esk4_3(X19,X20,X21)),X20)
        | X21 = k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_28,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))
      | m1_subset_1(k7_setfam_1(X28,X29),k1_zfmisc_1(k1_zfmisc_1(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_29,plain,(
    ! [X46,X47] :
      ( ( ~ m1_subset_1(X46,k1_zfmisc_1(X47))
        | r1_tarski(X46,X47) )
      & ( ~ r1_tarski(X46,X47)
        | m1_subset_1(X46,k1_zfmisc_1(X47)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_32,plain,(
    ! [X40] : r1_tarski(k1_xboole_0,X40) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_33,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k3_subset_1(X17,X18) = k4_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X45] : k4_xboole_0(X45,k1_xboole_0) = X45 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_40,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X9
        | X10 != k1_tarski(X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k1_tarski(X9) )
      & ( ~ r2_hidden(esk3_2(X13,X14),X14)
        | esk3_2(X13,X14) != X13
        | X14 = k1_tarski(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X14)
        | esk3_2(X13,X14) = X13
        | X14 = k1_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k1_tarski(X2)))
    | ~ r2_hidden(k3_subset_1(X2,X1),k1_tarski(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_50,plain,
    ( r2_hidden(k1_xboole_0,k7_setfam_1(X1,k1_tarski(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_44])])).

fof(c_0_51,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k7_setfam_1(X1,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_50])).

fof(c_0_53,plain,(
    ! [X56,X57] :
      ( ~ r2_hidden(X56,X57)
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_54,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k7_setfam_1(X1,k1_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_52])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_44]),c_0_26])).

cnf(c_0_59,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_54,c_0_55])]),c_0_34])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k7_setfam_1(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(k7_setfam_1(X1,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_50])).

fof(c_0_62,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 = k1_tarski(X1)
         => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t55_setfam_1])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_58])).

cnf(c_0_64,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_tarski(X1))
    | ~ r2_hidden(X2,k7_setfam_1(X1,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_42])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_60]),c_0_61])).

fof(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    & esk2_0 = k1_tarski(esk1_0)
    & k7_setfam_1(esk1_0,esk2_0) != k1_tarski(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_62])])])).

fof(c_0_67,plain,(
    ! [X41,X42] :
      ( ( k4_xboole_0(X41,X42) != k1_xboole_0
        | r1_tarski(X41,X42) )
      & ( ~ r1_tarski(X41,X42)
        | k4_xboole_0(X41,X42) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_69,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(X34)))
      | k7_setfam_1(X34,k7_setfam_1(X34,X35)) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_70,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_71,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk4_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_63])).

cnf(c_0_73,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_tarski(X1))
    | ~ r2_hidden(X2,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( esk2_0 = k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_25])).

cnf(c_0_77,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_79,plain,
    ( k1_tarski(k1_xboole_0) = k7_setfam_1(X1,X2)
    | r2_hidden(esk4_3(X1,X2,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | r2_hidden(k3_subset_1(X1,esk4_3(X1,X2,k1_tarski(k1_xboole_0))),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( k7_setfam_1(esk1_0,esk2_0) != k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk1_0,X1),esk2_0)
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(X1))
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_85,plain,
    ( m1_subset_1(k7_setfam_1(X1,k1_tarski(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_72])).

cnf(c_0_86,plain,
    ( k7_setfam_1(X1,k7_setfam_1(X1,k1_tarski(k1_xboole_0))) = k1_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_72])).

cnf(c_0_87,negated_conjecture,
    ( X1 = esk1_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk1_0,esk4_3(esk1_0,esk2_0,k1_tarski(k1_xboole_0))),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k1_tarski(k1_xboole_0)))
    | ~ r2_hidden(k3_subset_1(X2,X1),k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_72])).

cnf(c_0_90,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_83])).

cnf(c_0_91,plain,
    ( k1_tarski(k1_xboole_0) = k7_setfam_1(X1,X2)
    | m1_subset_1(esk4_3(X1,X2,k1_tarski(k1_xboole_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_72])).

cnf(c_0_92,plain,
    ( X3 = k7_setfam_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(k3_subset_1(X1,esk4_3(X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k1_tarski(k1_xboole_0))
    | ~ r2_hidden(k3_subset_1(X2,X1),k7_setfam_1(X2,k1_tarski(k1_xboole_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_85]),c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k3_subset_1(esk1_0,esk4_3(esk1_0,esk2_0,k1_tarski(k1_xboole_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k7_setfam_1(X1,k1_tarski(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_49]),c_0_25])])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk4_3(esk1_0,esk2_0,k1_tarski(k1_xboole_0)),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_80]),c_0_81])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(esk4_3(esk1_0,esk2_0,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_88]),c_0_72]),c_0_80])]),c_0_81])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_96])]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
