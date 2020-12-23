%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0962+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:59 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 347 expanded)
%              Number of clauses        :   49 ( 150 expanded)
%              Number of leaves         :   20 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  239 (1280 expanded)
%              Number of equality atoms :   64 ( 192 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',redefinition_k3_relset_1)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',dt_k3_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',dt_k4_relat_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',t14_relset_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t25_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t100_zfmisc_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

fof(c_0_21,plain,(
    ! [X101,X102,X103] :
      ( ~ v1_relat_1(X103)
      | ~ r1_tarski(k1_relat_1(X103),X101)
      | ~ r1_tarski(k2_relat_1(X103),X102)
      | m1_subset_1(X103,k1_zfmisc_1(k2_zfmisc_1(X101,X102))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(k2_relat_1(esk2_0),esk1_0)
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X913,X914] :
      ( ( r1_tarski(X913,X914)
        | X913 != X914 )
      & ( r1_tarski(X914,X913)
        | X913 != X914 )
      & ( ~ r1_tarski(X913,X914)
        | ~ r1_tarski(X914,X913)
        | X913 = X914 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X3879,X3880,X3881] :
      ( ~ m1_subset_1(X3881,k1_zfmisc_1(k2_zfmisc_1(X3879,X3880)))
      | k3_relset_1(X3879,X3880,X3881) = k4_relat_1(X3881) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X4268,X4269,X4270] :
      ( ~ m1_subset_1(X4270,k1_zfmisc_1(k2_zfmisc_1(X4268,X4269)))
      | m1_subset_1(k3_relset_1(X4268,X4269,X4270),k1_zfmisc_1(k2_zfmisc_1(X4269,X4268))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_32,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,plain,(
    ! [X69,X70] :
      ( ( ~ m1_subset_1(X69,k1_zfmisc_1(X70))
        | r1_tarski(X69,X70) )
      & ( ~ r1_tarski(X69,X70)
        | m1_subset_1(X69,k1_zfmisc_1(X70)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k3_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0) = k4_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X3874] :
      ( ( k2_relat_1(X3874) = k1_relat_1(k4_relat_1(X3874))
        | ~ v1_relat_1(X3874) )
      & ( k1_relat_1(X3874) = k2_relat_1(k4_relat_1(X3874))
        | ~ v1_relat_1(X3874) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_38,plain,(
    ! [X3872] :
      ( ~ v1_relat_1(X3872)
      | v1_relat_1(k4_relat_1(X3872)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_39,plain,(
    ! [X108,X109,X110,X111] :
      ( ~ m1_subset_1(X111,k1_zfmisc_1(k2_zfmisc_1(X110,X108)))
      | ~ r1_tarski(k2_relat_1(X111),X109)
      | m1_subset_1(X111,k1_zfmisc_1(k2_zfmisc_1(X110,X109))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

fof(c_0_40,plain,(
    ! [X505,X506] :
      ( ( r1_tarski(k1_relat_1(X505),k1_relat_1(X506))
        | ~ r1_tarski(X505,X506)
        | ~ v1_relat_1(X506)
        | ~ v1_relat_1(X505) )
      & ( r1_tarski(k2_relat_1(X505),k2_relat_1(X506))
        | ~ r1_tarski(X505,X506)
        | ~ v1_relat_1(X506)
        | ~ v1_relat_1(X505) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k4_relat_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_relat_1(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_36])).

cnf(c_0_43,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X343,X344] : v1_relat_1(k2_zfmisc_1(X343,X344)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_45,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k4_relat_1(esk2_0),k2_zfmisc_1(esk1_0,k1_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk2_0)) = k2_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_50,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),X1)))
    | ~ r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k2_zfmisc_1(esk1_0,k1_relat_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])])).

fof(c_0_56,plain,(
    ! [X3532,X3533,X3534] :
      ( ~ m1_subset_1(X3534,k1_zfmisc_1(k2_zfmisc_1(X3532,X3533)))
      | k1_relset_1(X3532,X3533,X3534) = k1_relat_1(X3534) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_57,plain,(
    ! [X147] : r1_tarski(X147,k1_zfmisc_1(k3_tarski(X147))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X791,X792,X793] :
      ( ( v1_funct_1(X793)
        | ~ v1_funct_1(X793)
        | ~ v1_partfun1(X793,X791)
        | ~ m1_subset_1(X793,k1_zfmisc_1(k2_zfmisc_1(X791,X792))) )
      & ( v1_funct_2(X793,X791,X792)
        | ~ v1_funct_1(X793)
        | ~ v1_partfun1(X793,X791)
        | ~ m1_subset_1(X793,k1_zfmisc_1(k2_zfmisc_1(X791,X792))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(k2_zfmisc_1(esk1_0,k1_relat_1(esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_61,plain,(
    ! [X794,X795,X796] :
      ( ( ~ v1_funct_2(X796,X794,X795)
        | X794 = k1_relset_1(X794,X795,X796)
        | X795 = k1_xboole_0
        | ~ m1_subset_1(X796,k1_zfmisc_1(k2_zfmisc_1(X794,X795))) )
      & ( X794 != k1_relset_1(X794,X795,X796)
        | v1_funct_2(X796,X794,X795)
        | X795 = k1_xboole_0
        | ~ m1_subset_1(X796,k1_zfmisc_1(k2_zfmisc_1(X794,X795))) )
      & ( ~ v1_funct_2(X796,X794,X795)
        | X794 = k1_relset_1(X794,X795,X796)
        | X794 != k1_xboole_0
        | ~ m1_subset_1(X796,k1_zfmisc_1(k2_zfmisc_1(X794,X795))) )
      & ( X794 != k1_relset_1(X794,X795,X796)
        | v1_funct_2(X796,X794,X795)
        | X794 != k1_xboole_0
        | ~ m1_subset_1(X796,k1_zfmisc_1(k2_zfmisc_1(X794,X795))) )
      & ( ~ v1_funct_2(X796,X794,X795)
        | X796 = k1_xboole_0
        | X794 = k1_xboole_0
        | X795 != k1_xboole_0
        | ~ m1_subset_1(X796,k1_zfmisc_1(k2_zfmisc_1(X794,X795))) )
      & ( X796 != k1_xboole_0
        | v1_funct_2(X796,X794,X795)
        | X794 = k1_xboole_0
        | X795 != k1_xboole_0
        | ~ m1_subset_1(X796,k1_zfmisc_1(k2_zfmisc_1(X794,X795))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_62,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_63,plain,(
    ! [X234,X235] :
      ( ( k2_zfmisc_1(X234,X235) != k1_xboole_0
        | X234 = k1_xboole_0
        | X235 = k1_xboole_0 )
      & ( X234 != k1_xboole_0
        | k2_zfmisc_1(X234,X235) = k1_xboole_0 )
      & ( X235 != k1_xboole_0
        | k2_zfmisc_1(X234,X235) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_64,plain,(
    ! [X3523,X3524,X3525] :
      ( ~ v1_xboole_0(X3523)
      | ~ m1_subset_1(X3525,k1_zfmisc_1(k2_zfmisc_1(X3523,X3524)))
      | v1_partfun1(X3525,X3523) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_33])])).

cnf(c_0_68,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(k2_zfmisc_1(esk1_0,k1_relat_1(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_60])).

cnf(c_0_70,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0) = k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_33])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_74,plain,(
    ! [X972] : r1_tarski(k1_xboole_0,X972) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_75,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k1_zfmisc_1(k3_tarski(k2_relat_1(esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_partfun1(esk2_0,k1_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_33]),c_0_53])]),c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(k2_zfmisc_1(esk1_0,k1_relat_1(esk2_0)))) = esk2_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(k2_zfmisc_1(esk1_0,k1_relat_1(esk2_0)))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_33])]),c_0_67])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81]),c_0_82]),c_0_79]),c_0_80]),c_0_81]),c_0_82]),c_0_83])])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_81]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
