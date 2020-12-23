%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t34_subset_1.p : TPTP v0.0.0. Released v0.0.0.
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

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 276 expanded)
%              Number of clauses        :   68 ( 122 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   18
%              Number of atoms          :  217 ( 578 expanded)
%              Number of equality atoms :   74 ( 179 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',d2_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',dt_k9_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',fc1_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',redefinition_k9_subset_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',commutativity_k3_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t7_boole)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',existence_m1_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',involutiveness_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',d5_subset_1)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',redefinition_k6_subset_1)).

fof(t34_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k5_subset_1(X1,X2,X3)) = k4_subset_1(X1,k9_subset_1(X1,X2,X3),k9_subset_1(X1,k3_subset_1(X1,X2),k3_subset_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t34_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',d1_zfmisc_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',dt_k3_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t3_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t28_xboole_1)).

fof(t102_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t102_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',commutativity_k2_xboole_0)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t53_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',idempotence_k3_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',t1_boole)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',redefinition_k4_subset_1)).

fof(redefinition_k5_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k5_subset_1(X1,X2,X3) = k5_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',redefinition_k5_subset_1)).

fof(dt_k5_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k5_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t34_subset_1.p',dt_k5_subset_1)).

fof(c_0_25,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X32,X31)
        | r2_hidden(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ r2_hidden(X32,X31)
        | m1_subset_1(X32,X31)
        | v1_xboole_0(X31) )
      & ( ~ m1_subset_1(X32,X31)
        | v1_xboole_0(X32)
        | ~ v1_xboole_0(X31) )
      & ( ~ v1_xboole_0(X32)
        | m1_subset_1(X32,X31)
        | ~ v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_26,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X45))
      | m1_subset_1(k9_subset_1(X45,X46,X47),k1_zfmisc_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_27,plain,(
    ! [X89] : ~ v1_xboole_0(k1_zfmisc_1(X89)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X68,X69,X70] :
      ( ~ m1_subset_1(X70,k1_zfmisc_1(X68))
      | k9_subset_1(X68,X69,X70) = k3_xboole_0(X69,X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_32,plain,(
    ! [X77] : k3_xboole_0(X77,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_33,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_34,plain,
    ( r2_hidden(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_35,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X85,X86] :
      ( ~ r2_hidden(X85,X86)
      | ~ v1_xboole_0(X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_39,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_41,plain,(
    ! [X48] : m1_subset_1(esk5_1(X48),X48) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_42,plain,(
    ! [X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(X58))
      | k3_subset_1(X58,k3_subset_1(X58,X59)) = X59 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_43,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,X34) = k4_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X43,X44] : m1_subset_1(k6_subset_1(X43,X44),k1_zfmisc_1(X43)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_49,plain,(
    ! [X66,X67] : k6_subset_1(X66,X67) = k4_xboole_0(X66,X67) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_50,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k3_subset_1(X1,k5_subset_1(X1,X2,X3)) = k4_subset_1(X1,k9_subset_1(X1,X2,X3),k9_subset_1(X1,k3_subset_1(X1,X2),k3_subset_1(X1,X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_subset_1])).

fof(c_0_51,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X26,X25)
        | r1_tarski(X26,X24)
        | X25 != k1_zfmisc_1(X24) )
      & ( ~ r1_tarski(X27,X24)
        | r2_hidden(X27,X25)
        | X25 != k1_zfmisc_1(X24) )
      & ( ~ r2_hidden(esk4_2(X28,X29),X29)
        | ~ r1_tarski(esk4_2(X28,X29),X28)
        | X29 = k1_zfmisc_1(X28) )
      & ( r2_hidden(esk4_2(X28,X29),X29)
        | r1_tarski(esk4_2(X28,X29),X28)
        | X29 = k1_zfmisc_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_52,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | m1_subset_1(k3_subset_1(X35,X36),k1_zfmisc_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_53,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_55,plain,(
    ! [X78] : k4_xboole_0(X78,k1_xboole_0) = X78 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) != k4_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0),k9_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).

fof(c_0_61,plain,(
    ! [X75,X76] :
      ( ~ r1_tarski(X75,X76)
      | k3_xboole_0(X75,X76) = X75 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k3_subset_1(X1,k4_xboole_0(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) != k4_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0),k9_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_63]),c_0_30])).

fof(c_0_73,plain,(
    ! [X71,X72,X73] : k4_xboole_0(X71,k5_xboole_0(X72,X73)) = k2_xboole_0(k4_xboole_0(X71,k2_xboole_0(X72,X73)),k3_xboole_0(k3_xboole_0(X71,X72),X73)) ),
    inference(variable_rename,[status(thm)],[t102_xboole_1])).

fof(c_0_74,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_75,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k2_xboole_0(X81,X82)) = k3_xboole_0(k4_xboole_0(X80,X81),k4_xboole_0(X80,X82)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

cnf(c_0_76,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( k4_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0),k9_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0))) != k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_54]),c_0_69])])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_53]),c_0_63])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_83,plain,(
    ! [X51] : k3_xboole_0(X51,X51) = X51 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_76]),c_0_77])])).

fof(c_0_86,plain,(
    ! [X74] : k2_xboole_0(X74,k1_xboole_0) = X74 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_87,negated_conjecture,
    ( k4_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0),k3_xboole_0(k4_xboole_0(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0))) != k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_35]),c_0_67])]),c_0_37])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_90,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_40])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( k4_subset_1(esk1_0,k9_subset_1(esk1_0,esk2_0,esk3_0),k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))) != k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_54]),c_0_84]),c_0_88])]),c_0_82])).

fof(c_0_95,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(X60))
      | ~ m1_subset_1(X62,k1_zfmisc_1(X60))
      | k4_subset_1(X60,X61,X62) = k2_xboole_0(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_88]),c_0_30])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_89])).

cnf(c_0_98,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k4_subset_1(esk1_0,k3_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))) != k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_35]),c_0_69])])).

cnf(c_0_100,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_96]),c_0_37])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_69])).

cnf(c_0_103,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))) != k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(k3_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_67])])).

cnf(c_0_105,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,X1))) = k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_102])).

cnf(c_0_107,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_37])).

cnf(c_0_108,negated_conjecture,
    ( k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) != k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ m1_subset_1(k3_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

fof(c_0_110,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X64,k1_zfmisc_1(X63))
      | ~ m1_subset_1(X65,k1_zfmisc_1(X63))
      | k5_subset_1(X63,X64,X65) = k5_xboole_0(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_subset_1])])).

cnf(c_0_111,negated_conjecture,
    ( k3_subset_1(esk1_0,k5_subset_1(esk1_0,esk2_0,esk3_0)) != k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109])])).

cnf(c_0_112,plain,
    ( k5_subset_1(X2,X1,X3) = k5_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

fof(c_0_113,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | m1_subset_1(k5_subset_1(X40,X41,X42),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_subset_1])])).

cnf(c_0_114,negated_conjecture,
    ( k3_subset_1(esk1_0,k5_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_69]),c_0_88])])).

cnf(c_0_115,plain,
    ( m1_subset_1(k5_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( ~ m1_subset_1(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_54])).

cnf(c_0_117,plain,
    ( m1_subset_1(k5_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_112])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_69]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
