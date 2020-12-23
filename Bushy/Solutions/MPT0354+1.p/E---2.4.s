%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t33_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:22 EDT 2019

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 319 expanded)
%              Number of clauses        :   60 ( 147 expanded)
%              Number of leaves         :   22 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 586 expanded)
%              Number of equality atoms :   68 ( 206 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k6_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t7_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t3_boole)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k9_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',fc1_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',involutiveness_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',d5_subset_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t52_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t4_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',commutativity_k2_xboole_0)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',dt_k7_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k7_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',dt_k3_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',dt_k9_subset_1)).

fof(t33_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t33_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',d1_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',commutativity_k3_xboole_0)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t33_subset_1.p',redefinition_k4_subset_1)).

fof(c_0_22,plain,(
    ! [X35,X36] : m1_subset_1(k6_subset_1(X35,X36),k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_23,plain,(
    ! [X58,X59] : k6_subset_1(X58,X59) = k4_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_24,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X27,X26)
        | r2_hidden(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ r2_hidden(X27,X26)
        | m1_subset_1(X27,X26)
        | v1_xboole_0(X26) )
      & ( ~ m1_subset_1(X27,X26)
        | v1_xboole_0(X27)
        | ~ v1_xboole_0(X26) )
      & ( ~ v1_xboole_0(X27)
        | m1_subset_1(X27,X26)
        | ~ v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_25,plain,(
    ! [X76,X77] :
      ( ~ r2_hidden(X76,X77)
      | ~ v1_xboole_0(X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X70] : k4_xboole_0(X70,k1_xboole_0) = X70 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_29,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X65,k1_zfmisc_1(X63))
      | k9_subset_1(X63,X64,X65) = k3_xboole_0(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X80] : ~ v1_xboole_0(k1_zfmisc_1(X80)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_35,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(X53))
      | k3_subset_1(X53,k3_subset_1(X53,X54)) = X54 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_36,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | k3_subset_1(X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_37,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X72,X73,X74] : k4_xboole_0(X72,k4_xboole_0(X73,X74)) = k2_xboole_0(k4_xboole_0(X72,X73),k3_xboole_0(X72,X74)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_43,plain,(
    ! [X71] : k4_xboole_0(k1_xboole_0,X71) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_44,plain,(
    ! [X66] : k2_xboole_0(X66,k1_xboole_0) = X66 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_45,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_46,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | m1_subset_1(k7_subset_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

fof(c_0_47,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(X60))
      | k7_subset_1(X60,X61,X62) = k4_xboole_0(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_48,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | m1_subset_1(k3_subset_1(X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_49,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_51,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | m1_subset_1(k9_subset_1(X40,X41,X42),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_52,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3)
    | ~ r2_hidden(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_58,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t33_subset_1])).

cnf(c_0_59,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_63,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_55])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_67,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X21,X20)
        | r1_tarski(X21,X19)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r1_tarski(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k1_zfmisc_1(X19) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | ~ r1_tarski(esk4_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) )
      & ( r2_hidden(esk4_2(X23,X24),X24)
        | r1_tarski(esk4_2(X23,X24),X23)
        | X24 = k1_zfmisc_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & k3_subset_1(esk1_0,k7_subset_1(esk1_0,esk2_0,esk3_0)) != k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).

cnf(c_0_69,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k3_subset_1(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_61])).

cnf(c_0_71,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_33])).

cnf(c_0_72,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_40])])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k3_subset_1(esk1_0,k7_subset_1(esk1_0,esk2_0,esk3_0)) != k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( k1_xboole_0 = k4_xboole_0(X1,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_71]),c_0_40])])).

cnf(c_0_80,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_81,plain,(
    ! [X67,X68] :
      ( ~ r1_tarski(X67,X68)
      | k3_xboole_0(X67,X68) = X67 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_75]),c_0_41])).

fof(c_0_84,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_85,negated_conjecture,
    ( k4_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),esk3_0) != k3_subset_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_60]),c_0_77])])).

fof(c_0_86,plain,(
    ! [X55,X56,X57] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(X55))
      | ~ m1_subset_1(X57,k1_zfmisc_1(X55))
      | k4_subset_1(X55,X56,X57) = k2_xboole_0(X56,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_88,plain,
    ( k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( k4_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0),esk3_0) != k3_subset_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_50]),c_0_77])])).

cnf(c_0_93,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_38])).

cnf(c_0_95,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_41])).

cnf(c_0_96,plain,
    ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_88]),c_0_66])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_75]),c_0_32])])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_97,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0) != k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_50]),c_0_99])])).

cnf(c_0_103,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,X1),esk3_0) = k4_xboole_0(esk1_0,k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])]),
    [proof]).
%------------------------------------------------------------------------------
