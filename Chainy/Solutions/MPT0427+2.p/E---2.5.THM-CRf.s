%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0427+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 172 expanded)
%              Number of clauses        :   38 (  70 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  165 ( 490 expanded)
%              Number of equality atoms :   40 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d2_subset_1)).

fof(dt_k8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k8_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',fc1_subset_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t69_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t66_xboole_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',l13_xboole_0)).

fof(t7_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_setfam_1(X1,X3),k8_setfam_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_setfam_1])).

fof(c_0_16,plain,(
    ! [X1575] : m1_subset_1(k2_subset_1(X1575),k1_zfmisc_1(X1575)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_17,plain,(
    ! [X1531] : k2_subset_1(X1531) = X1531 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_18,negated_conjecture,
    ( m1_subset_1(esk111_0,k1_zfmisc_1(k1_zfmisc_1(esk110_0)))
    & m1_subset_1(esk112_0,k1_zfmisc_1(k1_zfmisc_1(esk110_0)))
    & r1_tarski(esk111_0,esk112_0)
    & ~ r1_tarski(k8_setfam_1(esk110_0,esk112_0),k8_setfam_1(esk110_0,esk111_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X1838,X1839] :
      ( ( X1839 = k1_xboole_0
        | k8_setfam_1(X1838,X1839) = k6_setfam_1(X1838,X1839)
        | ~ m1_subset_1(X1839,k1_zfmisc_1(k1_zfmisc_1(X1838))) )
      & ( X1839 != k1_xboole_0
        | k8_setfam_1(X1838,X1839) = X1838
        | ~ m1_subset_1(X1839,k1_zfmisc_1(k1_zfmisc_1(X1838))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

fof(c_0_20,plain,(
    ! [X1994,X1995] :
      ( ( ~ m1_subset_1(X1994,k1_zfmisc_1(X1995))
        | r1_tarski(X1994,X1995) )
      & ( ~ r1_tarski(X1994,X1995)
        | m1_subset_1(X1994,k1_zfmisc_1(X1995)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X1962,X1963] :
      ( ~ r2_hidden(X1962,X1963)
      | m1_subset_1(X1962,X1963) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_22,plain,(
    ! [X1826,X1827] :
      ( ~ v1_xboole_0(X1826)
      | ~ m1_subset_1(X1827,k1_zfmisc_1(X1826))
      | v1_xboole_0(X1827) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk110_0,esk112_0),k8_setfam_1(esk110_0,esk111_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk111_0,k1_zfmisc_1(k1_zfmisc_1(esk110_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X1496,X1497] :
      ( ( ~ m1_subset_1(X1497,X1496)
        | r2_hidden(X1497,X1496)
        | v1_xboole_0(X1496) )
      & ( ~ r2_hidden(X1497,X1496)
        | m1_subset_1(X1497,X1496)
        | v1_xboole_0(X1496) )
      & ( ~ m1_subset_1(X1497,X1496)
        | v1_xboole_0(X1497)
        | ~ v1_xboole_0(X1496) )
      & ( ~ v1_xboole_0(X1497)
        | m1_subset_1(X1497,X1496)
        | ~ v1_xboole_0(X1496) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_31,plain,(
    ! [X1931,X1932] :
      ( ~ m1_subset_1(X1932,k1_zfmisc_1(k1_zfmisc_1(X1931)))
      | m1_subset_1(k8_setfam_1(X1931,X1932),k1_zfmisc_1(X1931)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_setfam_1])])).

fof(c_0_32,plain,(
    ! [X1600] : ~ v1_xboole_0(k1_zfmisc_1(X1600)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_35,plain,(
    ! [X347,X348] :
      ( v1_xboole_0(X348)
      | ~ r1_tarski(X348,X347)
      | ~ r1_xboole_0(X348,X347) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_36,plain,(
    ! [X340] :
      ( ( r1_xboole_0(X340,X340)
        | X340 != k1_xboole_0 )
      & ( X340 = k1_xboole_0
        | ~ r1_xboole_0(X340,X340) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_38,plain,(
    ! [X1947,X1948] :
      ( ~ m1_subset_1(X1948,k1_zfmisc_1(k1_zfmisc_1(X1947)))
      | k6_setfam_1(X1947,X1948) = k1_setfam_1(X1948) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_39,negated_conjecture,
    ( esk111_0 != k1_xboole_0
    | ~ r1_tarski(k8_setfam_1(esk110_0,esk112_0),esk110_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( m1_subset_1(k8_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk111_0,esk112_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk112_0,k1_zfmisc_1(k1_zfmisc_1(esk110_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( esk111_0 != k1_xboole_0
    | ~ r2_hidden(k8_setfam_1(esk110_0,esk112_0),k1_zfmisc_1(esk110_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,plain,
    ( r2_hidden(k8_setfam_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

fof(c_0_54,plain,(
    ! [X69] :
      ( ~ v1_xboole_0(X69)
      | X69 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(esk111_0)
    | ~ v1_xboole_0(esk112_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_57,negated_conjecture,
    ( esk112_0 != k1_xboole_0
    | ~ r1_tarski(esk110_0,k8_setfam_1(esk110_0,esk111_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_49])])).

cnf(c_0_58,plain,
    ( k8_setfam_1(X1,X2) = k1_setfam_1(X2)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( esk111_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_49])])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk111_0)
    | esk112_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk112_0 != k1_xboole_0
    | esk111_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_26]),c_0_48]),c_0_27])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(esk110_0,esk112_0),k1_setfam_1(esk111_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_58]),c_0_27])]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( esk112_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

fof(c_0_65,plain,(
    ! [X2054,X2055] :
      ( ~ r1_tarski(X2054,X2055)
      | X2054 = k1_xboole_0
      | r1_tarski(k1_setfam_1(X2055),k1_setfam_1(X2054)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_setfam_1])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk112_0),k1_setfam_1(esk111_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58]),c_0_49])]),c_0_64])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_45])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
