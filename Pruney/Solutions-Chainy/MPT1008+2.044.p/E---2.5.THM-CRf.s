%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 519 expanded)
%              Number of clauses        :   41 ( 198 expanded)
%              Number of leaves         :   17 ( 151 expanded)
%              Depth                    :   12
%              Number of atoms          :  263 (1041 expanded)
%              Number of equality atoms :  132 ( 630 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))
    & esk5_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_19,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | k1_relat_1(X25) != k1_tarski(X24)
      | k2_relat_1(X25) = k1_tarski(k1_funct_1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_23,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X16,k1_enumset1(X13,X14,X15))
        | X16 = k1_xboole_0
        | X16 = k1_tarski(X13)
        | X16 = k1_tarski(X14)
        | X16 = k1_tarski(X15)
        | X16 = k2_tarski(X13,X14)
        | X16 = k2_tarski(X14,X15)
        | X16 = k2_tarski(X13,X15)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( X16 != k1_xboole_0
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) )
      & ( X16 != k1_tarski(X13)
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) )
      & ( X16 != k1_tarski(X14)
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) )
      & ( X16 != k1_tarski(X15)
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) )
      & ( X16 != k2_tarski(X13,X14)
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) )
      & ( X16 != k2_tarski(X14,X15)
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) )
      & ( X16 != k2_tarski(X13,X15)
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) )
      & ( X16 != k1_enumset1(X13,X14,X15)
        | r1_tarski(X16,k1_enumset1(X13,X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X4)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X3,X4)
    | X1 = k2_tarski(X2,X4)
    | X1 = k1_enumset1(X2,X3,X4)
    | ~ r1_tarski(X1,k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X21,X22] :
      ( ( ~ v4_relat_1(X22,X21)
        | r1_tarski(k1_relat_1(X22),X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r1_tarski(k1_relat_1(X22),X21)
        | v4_relat_1(X22,X21)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_35,plain,(
    ! [X31,X32,X33] :
      ( ( v4_relat_1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v5_relat_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_36,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0) != k2_enumset1(k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_37,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | ~ r1_tarski(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_42,plain,(
    ! [X37,X38,X39,X41,X42] :
      ( ( r2_hidden(esk1_3(X37,X38,X39),X38)
        | k1_relset_1(X38,X37,X39) = X38
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37))) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X37,X38,X39),X41),X39)
        | k1_relset_1(X38,X37,X39) = X38
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37))) )
      & ( k1_relset_1(X38,X37,X39) != X38
        | ~ r2_hidden(X42,X38)
        | r2_hidden(k4_tarski(X42,esk2_4(X37,X38,X39,X42)),X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X4,X4,X4,X4)
    | X1 = k2_enumset1(X3,X3,X3,X4)
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X3,X4)
    | X1 = k2_enumset1(X2,X2,X2,X4)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0) != k2_relat_1(esk6_0)
    | k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_47,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X4,esk2_4(X2,X1,X3,X4)),X3)
    | k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_51,plain,(
    ! [X17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_52,plain,(
    ! [X49,X50,X51] :
      ( ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X51 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X51 != k1_xboole_0
        | v1_funct_2(X51,X49,X50)
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_53,plain,(
    ! [X23] :
      ( ( k1_relat_1(X23) != k1_xboole_0
        | X23 = k1_xboole_0
        | ~ v1_relat_1(X23) )
      & ( k2_relat_1(X23) != k1_xboole_0
        | X23 = k1_xboole_0
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_54,plain,
    ( k1_relat_1(X1) = k2_enumset1(X2,X2,X2,X2)
    | k1_relat_1(X1) = k2_enumset1(X3,X3,X3,X2)
    | k1_relat_1(X1) = k2_enumset1(X3,X3,X3,X3)
    | k1_relat_1(X1) = k2_enumset1(X4,X4,X3,X2)
    | k1_relat_1(X1) = k2_enumset1(X4,X4,X4,X2)
    | k1_relat_1(X1) = k2_enumset1(X4,X4,X4,X3)
    | k1_relat_1(X1) = k2_enumset1(X4,X4,X4,X4)
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k2_enumset1(X4,X4,X3,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( v4_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])])).

cnf(c_0_57,plain,
    ( k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,k4_tarski(X4,esk2_4(X2,X1,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_39])]),c_0_56])).

cnf(c_0_64,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) != X1
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_65,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_39])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_71,plain,(
    ! [X44,X46,X47,X48] :
      ( ( r2_hidden(esk3_1(X44),X44)
        | X44 = k1_xboole_0 )
      & ( ~ r2_hidden(X46,X44)
        | esk3_1(X44) != k3_mcart_1(X46,X47,X48)
        | X44 = k1_xboole_0 )
      & ( ~ r2_hidden(X47,X44)
        | esk3_1(X44) != k3_mcart_1(X46,X47,X48)
        | X44 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_73,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:39:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.19/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.37  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.19/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.37  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 0.19/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.37  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.37  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.19/0.37  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.19/0.37  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))))&(esk5_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.19/0.37  fof(c_0_19, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_20, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_21, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_22, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(k1_relat_1(X25)!=k1_tarski(X24)|k2_relat_1(X25)=k1_tarski(k1_funct_1(X25,X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.19/0.37  fof(c_0_23, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  fof(c_0_28, plain, ![X13, X14, X15, X16]:((~r1_tarski(X16,k1_enumset1(X13,X14,X15))|(X16=k1_xboole_0|X16=k1_tarski(X13)|X16=k1_tarski(X14)|X16=k1_tarski(X15)|X16=k2_tarski(X13,X14)|X16=k2_tarski(X14,X15)|X16=k2_tarski(X13,X15)|X16=k1_enumset1(X13,X14,X15)))&((((((((X16!=k1_xboole_0|r1_tarski(X16,k1_enumset1(X13,X14,X15)))&(X16!=k1_tarski(X13)|r1_tarski(X16,k1_enumset1(X13,X14,X15))))&(X16!=k1_tarski(X14)|r1_tarski(X16,k1_enumset1(X13,X14,X15))))&(X16!=k1_tarski(X15)|r1_tarski(X16,k1_enumset1(X13,X14,X15))))&(X16!=k2_tarski(X13,X14)|r1_tarski(X16,k1_enumset1(X13,X14,X15))))&(X16!=k2_tarski(X14,X15)|r1_tarski(X16,k1_enumset1(X13,X14,X15))))&(X16!=k2_tarski(X13,X15)|r1_tarski(X16,k1_enumset1(X13,X14,X15))))&(X16!=k1_enumset1(X13,X14,X15)|r1_tarski(X16,k1_enumset1(X13,X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (k2_relset_1(k1_tarski(esk4_0),esk5_0,esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_30, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.37  cnf(c_0_33, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k1_tarski(X4)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X3,X4)|X1=k2_tarski(X2,X4)|X1=k1_enumset1(X2,X3,X4)|~r1_tarski(X1,k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  fof(c_0_34, plain, ![X21, X22]:((~v4_relat_1(X22,X21)|r1_tarski(k1_relat_1(X22),X21)|~v1_relat_1(X22))&(~r1_tarski(k1_relat_1(X22),X21)|v4_relat_1(X22,X21)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.37  fof(c_0_35, plain, ![X31, X32, X33]:((v4_relat_1(X33,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v5_relat_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0)!=k2_enumset1(k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0),k1_funct_1(esk6_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.19/0.37  cnf(c_0_37, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.37  fof(c_0_40, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.37  fof(c_0_41, plain, ![X26, X27]:(~r2_hidden(X26,X27)|~r1_tarski(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.37  fof(c_0_42, plain, ![X37, X38, X39, X41, X42]:(((r2_hidden(esk1_3(X37,X38,X39),X38)|k1_relset_1(X38,X37,X39)=X38|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37))))&(~r2_hidden(k4_tarski(esk1_3(X37,X38,X39),X41),X39)|k1_relset_1(X38,X37,X39)=X38|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))))&(k1_relset_1(X38,X37,X39)!=X38|(~r2_hidden(X42,X38)|r2_hidden(k4_tarski(X42,esk2_4(X37,X38,X39,X42)),X39))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.19/0.37  cnf(c_0_43, plain, (X1=k1_xboole_0|X1=k2_enumset1(X4,X4,X4,X4)|X1=k2_enumset1(X3,X3,X3,X4)|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X3,X4)|X1=k2_enumset1(X2,X2,X2,X4)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_27])).
% 0.19/0.37  cnf(c_0_44, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_45, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (k2_relset_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0,esk6_0)!=k2_relat_1(esk6_0)|k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.19/0.37  cnf(c_0_47, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.37  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.37  cnf(c_0_49, plain, (r2_hidden(k4_tarski(X4,esk2_4(X2,X1,X3,X4)),X3)|k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.37  fof(c_0_50, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.37  fof(c_0_51, plain, ![X17]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.37  fof(c_0_52, plain, ![X49, X50, X51]:((((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))))&((~v1_funct_2(X51,X49,X50)|X51=k1_xboole_0|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X51!=k1_xboole_0|v1_funct_2(X51,X49,X50)|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.37  fof(c_0_53, plain, ![X23]:((k1_relat_1(X23)!=k1_xboole_0|X23=k1_xboole_0|~v1_relat_1(X23))&(k2_relat_1(X23)!=k1_xboole_0|X23=k1_xboole_0|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.37  cnf(c_0_54, plain, (k1_relat_1(X1)=k2_enumset1(X2,X2,X2,X2)|k1_relat_1(X1)=k2_enumset1(X3,X3,X3,X2)|k1_relat_1(X1)=k2_enumset1(X3,X3,X3,X3)|k1_relat_1(X1)=k2_enumset1(X4,X4,X3,X2)|k1_relat_1(X1)=k2_enumset1(X4,X4,X4,X2)|k1_relat_1(X1)=k2_enumset1(X4,X4,X4,X3)|k1_relat_1(X1)=k2_enumset1(X4,X4,X4,X4)|k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k2_enumset1(X4,X4,X3,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (v4_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_32])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32])])).
% 0.19/0.37  cnf(c_0_57, plain, (k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X3,k4_tarski(X4,esk2_4(X2,X1,X3,X4)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.37  cnf(c_0_58, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.37  cnf(c_0_59, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.37  cnf(c_0_60, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk6_0,k1_tarski(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_62, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_39])]), c_0_56])).
% 0.19/0.37  cnf(c_0_64, plain, (k1_relset_1(X1,X2,k1_xboole_0)!=X1|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.19/0.37  cnf(c_0_65, plain, (k1_relset_1(X1,X2,k1_xboole_0)=X1|X2=k1_xboole_0|~v1_funct_2(k1_xboole_0,X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_39])])).
% 0.19/0.37  cnf(c_0_68, plain, (X1=k1_xboole_0|~v1_funct_2(k1_xboole_0,X2,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.37  cnf(c_0_69, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.37  cnf(c_0_70, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  fof(c_0_71, plain, ![X44, X46, X47, X48]:((r2_hidden(esk3_1(X44),X44)|X44=k1_xboole_0)&((~r2_hidden(X46,X44)|esk3_1(X44)!=k3_mcart_1(X46,X47,X48)|X44=k1_xboole_0)&(~r2_hidden(X47,X44)|esk3_1(X44)!=k3_mcart_1(X46,X47,X48)|X44=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.19/0.37  cnf(c_0_72, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.19/0.37  cnf(c_0_73, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.37  cnf(c_0_74, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_63])).
% 0.19/0.37  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 76
% 0.19/0.37  # Proof object clause steps            : 41
% 0.19/0.37  # Proof object formula steps           : 35
% 0.19/0.37  # Proof object conjectures             : 21
% 0.19/0.37  # Proof object clause conjectures      : 18
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 21
% 0.19/0.37  # Proof object initial formulas used   : 17
% 0.19/0.37  # Proof object generating inferences   : 13
% 0.19/0.37  # Proof object simplifying inferences  : 51
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 18
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 42
% 0.19/0.37  # Removed in clause preprocessing      : 3
% 0.19/0.37  # Initial clauses in saturation        : 39
% 0.19/0.37  # Processed clauses                    : 131
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 17
% 0.19/0.37  # ...remaining for further processing  : 113
% 0.19/0.37  # Other redundant clauses eliminated   : 13
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 11
% 0.19/0.37  # Backward-rewritten                   : 15
% 0.19/0.37  # Generated clauses                    : 128
% 0.19/0.37  # ...of the previous two non-trivial   : 123
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 116
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 13
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 75
% 0.19/0.37  #    Positive orientable unit clauses  : 19
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 5
% 0.19/0.37  #    Non-unit-clauses                  : 51
% 0.19/0.37  # Current number of unprocessed clauses: 16
% 0.19/0.37  # ...number of literals in the above   : 91
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 29
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 688
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 366
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 26
% 0.19/0.37  # Unit Clause-clause subsumption calls : 66
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 26
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 5577
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.039 s
% 0.19/0.38  # System time              : 0.002 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
