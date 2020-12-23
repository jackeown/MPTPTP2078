%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:25 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  137 (2995 expanded)
%              Number of clauses        :   97 (1538 expanded)
%              Number of leaves         :   20 ( 845 expanded)
%              Depth                    :   22
%              Number of atoms          :  297 (7020 expanded)
%              Number of equality atoms :   53 (1402 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(fc11_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t49_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
             => ~ ( k1_relset_1(X1,X2,X3) != k1_xboole_0
                  & ! [X4] :
                      ( m1_subset_1(X4,X2)
                     => ~ r2_hidden(X4,k2_relset_1(X1,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(t24_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k1_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k2_relset_1(X1,X2,X3)
        & k2_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc8_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | X9 = X10
      | ~ v1_xboole_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_21,plain,(
    ! [X34] :
      ( ~ v1_xboole_0(X34)
      | v1_xboole_0(k2_relat_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_24,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

fof(c_0_28,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X23] : ~ v1_xboole_0(k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_31,plain,(
    ! [X22] : k3_tarski(k1_zfmisc_1(X22)) = X22 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_32,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | v1_relat_1(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_39,plain,(
    ! [X35,X36] : v1_relat_1(k2_zfmisc_1(X35,X36)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
               => ~ ( k1_relset_1(X1,X2,X3) != k1_xboole_0
                    & ! [X4] :
                        ( m1_subset_1(X4,X2)
                       => ~ r2_hidden(X4,k2_relset_1(X1,X2,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_relset_1])).

cnf(c_0_41,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | r2_hidden(esk4_2(X1,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_32]),c_0_32]),c_0_32]),c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_47,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,negated_conjecture,(
    ! [X59] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & k1_relset_1(esk5_0,esk6_0,esk7_0) != k1_xboole_0
      & ( ~ m1_subset_1(X59,esk6_0)
        | ~ r2_hidden(X59,k2_relset_1(esk5_0,esk6_0,esk7_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])])).

cnf(c_0_50,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk4_2(k1_zfmisc_1(X1),k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | r2_hidden(esk3_2(X1,k1_xboole_0),esk4_2(X1,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_43]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_34])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk1_1(k1_zfmisc_1(X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_41])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_1(esk1_1(k1_zfmisc_1(X1))),esk1_1(k1_zfmisc_1(X1)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_54,plain,(
    ! [X32,X33] :
      ( ( ~ v5_relat_1(X33,X32)
        | r1_tarski(k2_relat_1(X33),X32)
        | ~ v1_relat_1(X33) )
      & ( ~ r1_tarski(k2_relat_1(X33),X32)
        | v5_relat_1(X33,X32)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_55,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_58,plain,
    ( r2_hidden(esk4_2(k1_zfmisc_1(k1_zfmisc_1(X1)),k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_50]),c_0_23])])).

cnf(c_0_59,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_zfmisc_1(X1),k1_xboole_0),esk4_2(k1_zfmisc_1(X1),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_51])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_1(esk1_1(k1_zfmisc_1(X1))),X1)
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_61,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k2_relset_1(X47,X48,X49) = k2_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,esk4_2(k1_zfmisc_1(k1_zfmisc_1(X2)),k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_58]),c_0_41])).

cnf(c_0_66,plain,
    ( X1 = X2
    | r2_hidden(esk1_1(X2),X2)
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_46])).

cnf(c_0_67,plain,
    ( r2_hidden(esk3_2(k1_zfmisc_1(X1),k1_xboole_0),esk4_2(k1_zfmisc_1(X1),k1_xboole_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_59])).

cnf(c_0_68,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_60])).

fof(c_0_69,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | m1_subset_1(k3_relset_1(X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X42,X41))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

fof(c_0_70,plain,(
    ! [X53,X54,X55] :
      ( ( k1_relset_1(X54,X53,k3_relset_1(X53,X54,X55)) = k2_relset_1(X53,X54,X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( k2_relset_1(X54,X53,k3_relset_1(X53,X54,X55)) = k1_relset_1(X53,X54,X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relset_1])])])).

cnf(c_0_71,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_72,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),X1)
    | ~ v5_relat_1(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( v5_relat_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_56])).

fof(c_0_75,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | m1_subset_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_76,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | r2_hidden(X2,k1_zfmisc_1(X3))
    | ~ r2_hidden(X2,esk4_2(k1_zfmisc_1(k1_zfmisc_1(X3)),X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_34])).

cnf(c_0_77,plain,
    ( r2_hidden(esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0),esk4_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_79,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k1_relset_1(X44,X45,X46) = k1_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_80,plain,
    ( k1_relset_1(X1,X2,k3_relset_1(X2,X1,X3)) = k2_relset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = k2_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_56])).

fof(c_0_82,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,plain,
    ( r2_hidden(esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_34])).

fof(c_0_87,plain,(
    ! [X37] :
      ( v1_xboole_0(X37)
      | ~ v1_relat_1(X37)
      | ~ v1_xboole_0(k1_relat_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k3_relset_1(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_56])).

cnf(c_0_89,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_90,negated_conjecture,
    ( k1_relset_1(esk6_0,esk5_0,k3_relset_1(esk5_0,esk6_0,esk7_0)) = k2_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_56]),c_0_81])).

cnf(c_0_91,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,plain,
    ( m1_subset_1(esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(X1,esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_86]),c_0_41]),c_0_34])).

cnf(c_0_95,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(k3_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(k3_relset_1(esk5_0,esk6_0,esk7_0)) = k2_relat_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_88]),c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_36])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_66]),c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(k3_relset_1(esk5_0,esk6_0,esk7_0))
    | ~ v1_xboole_0(k2_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_101,plain,
    ( k2_relat_1(X1) = X1
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_46])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_98]),c_0_41])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_99]),c_0_36])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0)
    | v1_xboole_0(k3_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_37])).

cnf(c_0_105,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,k2_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(esk1_1(k2_relat_1(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( k3_relset_1(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_104])).

cnf(c_0_108,plain,
    ( k2_relset_1(X1,X2,k3_relset_1(X2,X1,X3)) = k1_relset_1(X2,X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_109,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_105,c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk1_1(k2_relat_1(esk7_0)),esk6_0)
    | r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_46])).

cnf(c_0_112,negated_conjecture,
    ( k1_relat_1(k3_relset_1(esk5_0,esk6_0,k1_xboole_0)) = k1_xboole_0
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_46]),c_0_32])).

cnf(c_0_113,negated_conjecture,
    ( k3_relset_1(esk5_0,esk6_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_46]),c_0_34])).

cnf(c_0_114,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_115,negated_conjecture,
    ( k2_relset_1(esk6_0,esk5_0,k3_relset_1(esk5_0,esk6_0,esk7_0)) = k1_relset_1(esk5_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_56])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_103])).

cnf(c_0_117,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(esk5_0,esk6_0,k1_xboole_0)
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0)
    | k1_relset_1(esk5_0,esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_46])).

cnf(c_0_120,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_relset_1(esk5_0,esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_56])).

cnf(c_0_121,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_37])).

cnf(c_0_122,negated_conjecture,
    ( k2_relat_1(k3_relset_1(esk5_0,esk6_0,esk7_0)) = k1_relset_1(esk5_0,esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_88]),c_0_115])).

cnf(c_0_123,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_116]),c_0_41]),c_0_34])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k1_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_63]),c_0_120])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk1_1(k3_relset_1(esk5_0,esk6_0,esk7_0)),k3_relset_1(esk5_0,esk6_0,esk7_0))
    | v1_xboole_0(k1_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( v1_xboole_0(k3_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_46]),c_0_23])]),c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk1_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_124])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk1_1(esk1_1(esk7_0)),esk1_1(esk7_0))
    | r2_hidden(k1_xboole_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_46])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk1_1(k3_relset_1(esk5_0,esk6_0,esk7_0)),k3_relset_1(esk5_0,esk6_0,esk7_0))
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( ~ r2_hidden(X1,k3_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk1_1(esk1_1(esk7_0)),k3_tarski(esk7_0))
    | r2_hidden(k1_xboole_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,k1_xboole_0),esk7_0)
    | r2_hidden(k1_xboole_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_42]),c_0_34])).

cnf(c_0_135,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_134,c_0_135]),c_0_135]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n012.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 17:05:52 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.12/0.31  # No SInE strategy applied
% 0.12/0.31  # Trying AutoSched0 for 299 seconds
% 1.22/1.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 1.22/1.38  # and selection function SelectCQIArEqFirst.
% 1.22/1.38  #
% 1.22/1.38  # Preprocessing time       : 0.028 s
% 1.22/1.38  # Presaturation interreduction done
% 1.22/1.38  
% 1.22/1.38  # Proof found!
% 1.22/1.38  # SZS status Theorem
% 1.22/1.38  # SZS output start CNFRefutation
% 1.22/1.38  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.22/1.38  fof(fc11_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.22/1.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.22/1.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.22/1.38  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 1.22/1.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.22/1.38  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.22/1.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.22/1.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.22/1.38  fof(t49_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 1.22/1.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.22/1.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.22/1.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.22/1.38  fof(dt_k3_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 1.22/1.38  fof(t24_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k1_relset_1(X2,X1,k3_relset_1(X1,X2,X3))=k2_relset_1(X1,X2,X3)&k2_relset_1(X2,X1,k3_relset_1(X1,X2,X3))=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 1.22/1.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.22/1.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.22/1.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.22/1.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.22/1.38  fof(fc8_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.22/1.38  fof(c_0_20, plain, ![X9, X10]:(~v1_xboole_0(X9)|X9=X10|~v1_xboole_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 1.22/1.38  fof(c_0_21, plain, ![X34]:(~v1_xboole_0(X34)|v1_xboole_0(k2_relat_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).
% 1.22/1.38  cnf(c_0_22, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.22/1.38  cnf(c_0_23, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.22/1.38  cnf(c_0_24, plain, (v1_xboole_0(k2_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.22/1.38  fof(c_0_25, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.22/1.38  cnf(c_0_26, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.22/1.38  cnf(c_0_27, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 1.22/1.38  fof(c_0_28, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(X13,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k3_tarski(X11))&(r2_hidden(esk2_3(X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k3_tarski(X11)))&(~r2_hidden(X15,X16)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k3_tarski(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|(~r2_hidden(esk3_2(X17,X18),X20)|~r2_hidden(X20,X17))|X18=k3_tarski(X17))&((r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))&(r2_hidden(esk4_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 1.22/1.38  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.22/1.38  fof(c_0_30, plain, ![X23]:~v1_xboole_0(k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.22/1.38  fof(c_0_31, plain, ![X22]:k3_tarski(k1_zfmisc_1(X22))=X22, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 1.22/1.38  cnf(c_0_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.22/1.38  cnf(c_0_33, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.22/1.38  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 1.22/1.38  cnf(c_0_35, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.22/1.38  cnf(c_0_36, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.22/1.38  cnf(c_0_37, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.22/1.38  fof(c_0_38, plain, ![X30, X31]:(~v1_relat_1(X30)|(~m1_subset_1(X31,k1_zfmisc_1(X30))|v1_relat_1(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.22/1.38  fof(c_0_39, plain, ![X35, X36]:v1_relat_1(k2_zfmisc_1(X35,X36)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.22/1.38  fof(c_0_40, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3)))))))))), inference(assume_negation,[status(cth)],[t49_relset_1])).
% 1.22/1.38  cnf(c_0_41, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.22/1.38  cnf(c_0_42, plain, (k3_tarski(X1)=k1_xboole_0|r2_hidden(esk4_2(X1,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_32]), c_0_32]), c_0_32]), c_0_34])).
% 1.22/1.38  cnf(c_0_43, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.22/1.38  cnf(c_0_44, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_35])).
% 1.22/1.38  cnf(c_0_45, plain, (r2_hidden(esk1_1(k1_zfmisc_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.22/1.38  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 1.22/1.38  cnf(c_0_47, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.22/1.38  cnf(c_0_48, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.22/1.38  fof(c_0_49, negated_conjecture, ![X59]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))&(k1_relset_1(esk5_0,esk6_0,esk7_0)!=k1_xboole_0&(~m1_subset_1(X59,esk6_0)|~r2_hidden(X59,k2_relset_1(esk5_0,esk6_0,esk7_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])])).
% 1.22/1.38  cnf(c_0_50, plain, (k1_xboole_0=X1|r2_hidden(esk4_2(k1_zfmisc_1(X1),k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.22/1.38  cnf(c_0_51, plain, (k3_tarski(X1)=k1_xboole_0|r2_hidden(esk3_2(X1,k1_xboole_0),esk4_2(X1,k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_43]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_34])).
% 1.22/1.38  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,esk1_1(k1_zfmisc_1(X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_41])).
% 1.22/1.38  cnf(c_0_53, plain, (r2_hidden(esk1_1(esk1_1(k1_zfmisc_1(X1))),esk1_1(k1_zfmisc_1(X1)))|r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.22/1.38  fof(c_0_54, plain, ![X32, X33]:((~v5_relat_1(X33,X32)|r1_tarski(k2_relat_1(X33),X32)|~v1_relat_1(X33))&(~r1_tarski(k2_relat_1(X33),X32)|v5_relat_1(X33,X32)|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 1.22/1.38  cnf(c_0_55, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.22/1.38  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.22/1.38  fof(c_0_57, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.22/1.38  cnf(c_0_58, plain, (r2_hidden(esk4_2(k1_zfmisc_1(k1_zfmisc_1(X1)),k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_50]), c_0_23])])).
% 1.22/1.38  cnf(c_0_59, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_zfmisc_1(X1),k1_xboole_0),esk4_2(k1_zfmisc_1(X1),k1_xboole_0))), inference(spm,[status(thm)],[c_0_41, c_0_51])).
% 1.22/1.38  cnf(c_0_60, plain, (r2_hidden(esk1_1(esk1_1(k1_zfmisc_1(X1))),X1)|r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.22/1.38  fof(c_0_61, plain, ![X47, X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k2_relset_1(X47,X48,X49)=k2_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.22/1.38  cnf(c_0_62, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.22/1.38  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.22/1.38  cnf(c_0_64, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.22/1.38  cnf(c_0_65, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,esk4_2(k1_zfmisc_1(k1_zfmisc_1(X2)),k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_58]), c_0_41])).
% 1.22/1.38  cnf(c_0_66, plain, (X1=X2|r2_hidden(esk1_1(X2),X2)|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_46, c_0_46])).
% 1.22/1.38  cnf(c_0_67, plain, (r2_hidden(esk3_2(k1_zfmisc_1(X1),k1_xboole_0),esk4_2(k1_zfmisc_1(X1),k1_xboole_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_59])).
% 1.22/1.38  cnf(c_0_68, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_34, c_0_60])).
% 1.22/1.38  fof(c_0_69, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|m1_subset_1(k3_relset_1(X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X42,X41)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).
% 1.22/1.38  fof(c_0_70, plain, ![X53, X54, X55]:((k1_relset_1(X54,X53,k3_relset_1(X53,X54,X55))=k2_relset_1(X53,X54,X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))&(k2_relset_1(X54,X53,k3_relset_1(X53,X54,X55))=k1_relset_1(X53,X54,X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_relset_1])])])).
% 1.22/1.38  cnf(c_0_71, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.22/1.38  fof(c_0_72, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.22/1.38  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),X1)|~v5_relat_1(esk7_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.22/1.38  cnf(c_0_74, negated_conjecture, (v5_relat_1(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_56])).
% 1.22/1.38  fof(c_0_75, plain, ![X24, X25]:(~r2_hidden(X24,X25)|m1_subset_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 1.22/1.38  cnf(c_0_76, plain, (r2_hidden(esk1_1(X1),X1)|r2_hidden(X2,k1_zfmisc_1(X3))|~r2_hidden(X2,esk4_2(k1_zfmisc_1(k1_zfmisc_1(X3)),X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_34])).
% 1.22/1.38  cnf(c_0_77, plain, (r2_hidden(esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0),esk4_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.22/1.38  cnf(c_0_78, plain, (m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.22/1.38  fof(c_0_79, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k1_relset_1(X44,X45,X46)=k1_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.22/1.38  cnf(c_0_80, plain, (k1_relset_1(X1,X2,k3_relset_1(X2,X1,X3))=k2_relset_1(X2,X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.22/1.38  cnf(c_0_81, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)=k2_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_71, c_0_56])).
% 1.22/1.38  fof(c_0_82, plain, ![X26, X27]:(~m1_subset_1(X26,X27)|(v1_xboole_0(X27)|r2_hidden(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 1.22/1.38  cnf(c_0_83, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.22/1.38  cnf(c_0_84, negated_conjecture, (r1_tarski(k2_relat_1(esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 1.22/1.38  cnf(c_0_85, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.22/1.38  cnf(c_0_86, plain, (r2_hidden(esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_34])).
% 1.22/1.38  fof(c_0_87, plain, ![X37]:(v1_xboole_0(X37)|~v1_relat_1(X37)|~v1_xboole_0(k1_relat_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).
% 1.22/1.38  cnf(c_0_88, negated_conjecture, (m1_subset_1(k3_relset_1(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(spm,[status(thm)],[c_0_78, c_0_56])).
% 1.22/1.38  cnf(c_0_89, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 1.22/1.38  cnf(c_0_90, negated_conjecture, (k1_relset_1(esk6_0,esk5_0,k3_relset_1(esk5_0,esk6_0,esk7_0))=k2_relat_1(esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_56]), c_0_81])).
% 1.22/1.38  cnf(c_0_91, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.22/1.38  cnf(c_0_92, negated_conjecture, (m1_subset_1(k2_relat_1(esk7_0),k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.22/1.38  cnf(c_0_93, plain, (m1_subset_1(esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 1.22/1.38  cnf(c_0_94, plain, (~r2_hidden(X1,esk3_2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_86]), c_0_41]), c_0_34])).
% 1.22/1.38  cnf(c_0_95, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 1.22/1.38  cnf(c_0_96, negated_conjecture, (v1_relat_1(k3_relset_1(esk5_0,esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_55, c_0_88])).
% 1.22/1.38  cnf(c_0_97, negated_conjecture, (k1_relat_1(k3_relset_1(esk5_0,esk6_0,esk7_0))=k2_relat_1(esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_88]), c_0_90])).
% 1.22/1.38  cnf(c_0_98, negated_conjecture, (r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_36])).
% 1.22/1.38  cnf(c_0_99, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|r2_hidden(esk1_1(X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_66]), c_0_94])).
% 1.22/1.38  cnf(c_0_100, negated_conjecture, (v1_xboole_0(k3_relset_1(esk5_0,esk6_0,esk7_0))|~v1_xboole_0(k2_relat_1(esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 1.22/1.38  cnf(c_0_101, plain, (k2_relat_1(X1)=X1|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_32, c_0_46])).
% 1.22/1.38  cnf(c_0_102, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_98]), c_0_41])).
% 1.22/1.38  cnf(c_0_103, plain, (r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))|r2_hidden(esk1_1(X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_99]), c_0_36])).
% 1.22/1.38  cnf(c_0_104, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk7_0)|v1_xboole_0(k3_relset_1(esk5_0,esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_37])).
% 1.22/1.38  cnf(c_0_105, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(X1,k2_relset_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.22/1.38  cnf(c_0_106, negated_conjecture, (r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(k1_xboole_0))|r2_hidden(esk1_1(k2_relat_1(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 1.22/1.38  cnf(c_0_107, negated_conjecture, (k3_relset_1(esk5_0,esk6_0,esk7_0)=k1_xboole_0|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_104])).
% 1.22/1.38  cnf(c_0_108, plain, (k2_relset_1(X1,X2,k3_relset_1(X2,X1,X3))=k1_relset_1(X2,X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.22/1.38  cnf(c_0_109, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_105, c_0_81])).
% 1.22/1.38  cnf(c_0_110, negated_conjecture, (m1_subset_1(esk1_1(k2_relat_1(esk7_0)),esk6_0)|r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_85, c_0_106])).
% 1.22/1.38  cnf(c_0_111, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_46])).
% 1.22/1.38  cnf(c_0_112, negated_conjecture, (k1_relat_1(k3_relset_1(esk5_0,esk6_0,k1_xboole_0))=k1_xboole_0|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_46]), c_0_32])).
% 1.22/1.38  cnf(c_0_113, negated_conjecture, (k3_relset_1(esk5_0,esk6_0,k1_xboole_0)=k1_xboole_0|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_46]), c_0_34])).
% 1.22/1.38  cnf(c_0_114, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.22/1.38  cnf(c_0_115, negated_conjecture, (k2_relset_1(esk6_0,esk5_0,k3_relset_1(esk5_0,esk6_0,esk7_0))=k1_relset_1(esk5_0,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_108, c_0_56])).
% 1.22/1.38  cnf(c_0_116, negated_conjecture, (r2_hidden(k2_relat_1(esk7_0),k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_103])).
% 1.22/1.38  cnf(c_0_117, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_relset_1(esk5_0,esk6_0,k1_xboole_0)|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_111])).
% 1.22/1.38  cnf(c_0_118, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(esk1_1(esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 1.22/1.38  cnf(c_0_119, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk7_0)|k1_relset_1(esk5_0,esk6_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_46])).
% 1.22/1.38  cnf(c_0_120, negated_conjecture, (k1_relat_1(esk7_0)=k1_relset_1(esk5_0,esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_56])).
% 1.22/1.38  cnf(c_0_121, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_37])).
% 1.22/1.38  cnf(c_0_122, negated_conjecture, (k2_relat_1(k3_relset_1(esk5_0,esk6_0,esk7_0))=k1_relset_1(esk5_0,esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_88]), c_0_115])).
% 1.22/1.38  cnf(c_0_123, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_116]), c_0_41]), c_0_34])).
% 1.22/1.38  cnf(c_0_124, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119])).
% 1.22/1.38  cnf(c_0_125, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k1_relset_1(esk5_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_63]), c_0_120])).
% 1.22/1.38  cnf(c_0_126, negated_conjecture, (r2_hidden(esk1_1(k3_relset_1(esk5_0,esk6_0,esk7_0)),k3_relset_1(esk5_0,esk6_0,esk7_0))|v1_xboole_0(k1_relset_1(esk5_0,esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 1.22/1.38  cnf(c_0_127, negated_conjecture, (v1_xboole_0(k3_relset_1(esk5_0,esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_46]), c_0_23])]), c_0_123])).
% 1.22/1.38  cnf(c_0_128, negated_conjecture, (r2_hidden(X1,k3_tarski(esk7_0))|~r2_hidden(X1,esk1_1(esk7_0))), inference(spm,[status(thm)],[c_0_44, c_0_124])).
% 1.22/1.38  cnf(c_0_129, negated_conjecture, (r2_hidden(esk1_1(esk1_1(esk7_0)),esk1_1(esk7_0))|r2_hidden(k1_xboole_0,esk7_0)), inference(spm,[status(thm)],[c_0_124, c_0_46])).
% 1.22/1.38  cnf(c_0_130, negated_conjecture, (r2_hidden(esk1_1(k3_relset_1(esk5_0,esk6_0,esk7_0)),k3_relset_1(esk5_0,esk6_0,esk7_0))|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 1.22/1.38  cnf(c_0_131, negated_conjecture, (~r2_hidden(X1,k3_relset_1(esk5_0,esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_127])).
% 1.22/1.38  cnf(c_0_132, negated_conjecture, (r2_hidden(esk1_1(esk1_1(esk7_0)),k3_tarski(esk7_0))|r2_hidden(k1_xboole_0,esk7_0)), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 1.22/1.38  cnf(c_0_133, negated_conjecture, (v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[c_0_130, c_0_131])).
% 1.22/1.38  cnf(c_0_134, negated_conjecture, (r2_hidden(esk4_2(esk7_0,k1_xboole_0),esk7_0)|r2_hidden(k1_xboole_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_42]), c_0_34])).
% 1.22/1.38  cnf(c_0_135, negated_conjecture, (~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_133])).
% 1.22/1.38  cnf(c_0_136, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_134, c_0_135]), c_0_135]), ['proof']).
% 1.22/1.38  # SZS output end CNFRefutation
% 1.22/1.38  # Proof object total steps             : 137
% 1.22/1.38  # Proof object clause steps            : 97
% 1.22/1.38  # Proof object formula steps           : 40
% 1.22/1.38  # Proof object conjectures             : 48
% 1.22/1.38  # Proof object clause conjectures      : 45
% 1.22/1.38  # Proof object formula conjectures     : 3
% 1.22/1.38  # Proof object initial clauses used    : 26
% 1.22/1.38  # Proof object initial formulas used   : 20
% 1.22/1.38  # Proof object generating inferences   : 67
% 1.22/1.38  # Proof object simplifying inferences  : 42
% 1.22/1.38  # Training examples: 0 positive, 0 negative
% 1.22/1.38  # Parsed axioms                        : 21
% 1.22/1.38  # Removed by relevancy pruning/SinE    : 0
% 1.22/1.38  # Initial clauses                      : 35
% 1.22/1.38  # Removed in clause preprocessing      : 0
% 1.22/1.38  # Initial clauses in saturation        : 35
% 1.22/1.38  # Processed clauses                    : 3685
% 1.22/1.38  # ...of these trivial                  : 353
% 1.22/1.38  # ...subsumed                          : 1848
% 1.22/1.38  # ...remaining for further processing  : 1484
% 1.22/1.38  # Other redundant clauses eliminated   : 254
% 1.22/1.38  # Clauses deleted for lack of memory   : 0
% 1.22/1.38  # Backward-subsumed                    : 139
% 1.22/1.38  # Backward-rewritten                   : 223
% 1.22/1.38  # Generated clauses                    : 163547
% 1.22/1.38  # ...of the previous two non-trivial   : 122649
% 1.22/1.38  # Contextual simplify-reflections      : 12
% 1.22/1.38  # Paramodulations                      : 163239
% 1.22/1.38  # Factorizations                       : 0
% 1.22/1.38  # Equation resolutions                 : 254
% 1.22/1.38  # Propositional unsat checks           : 0
% 1.22/1.38  #    Propositional check models        : 0
% 1.22/1.38  #    Propositional check unsatisfiable : 0
% 1.22/1.38  #    Propositional clauses             : 0
% 1.22/1.38  #    Propositional clauses after purity: 0
% 1.22/1.38  #    Propositional unsat core size     : 0
% 1.22/1.38  #    Propositional preprocessing time  : 0.000
% 1.22/1.38  #    Propositional encoding time       : 0.000
% 1.22/1.38  #    Propositional solver time         : 0.000
% 1.22/1.38  #    Success case prop preproc time    : 0.000
% 1.22/1.38  #    Success case prop encoding time   : 0.000
% 1.22/1.38  #    Success case prop solver time     : 0.000
% 1.22/1.38  # Current number of processed clauses  : 1030
% 1.22/1.38  #    Positive orientable unit clauses  : 367
% 1.22/1.38  #    Positive unorientable unit clauses: 2
% 1.22/1.38  #    Negative unit clauses             : 16
% 1.22/1.38  #    Non-unit-clauses                  : 645
% 1.22/1.38  # Current number of unprocessed clauses: 118241
% 1.22/1.38  # ...number of literals in the above   : 479175
% 1.22/1.38  # Current number of archived formulas  : 0
% 1.22/1.38  # Current number of archived clauses   : 451
% 1.22/1.38  # Clause-clause subsumption calls (NU) : 93141
% 1.22/1.38  # Rec. Clause-clause subsumption calls : 59802
% 1.22/1.38  # Non-unit clause-clause subsumptions  : 1703
% 1.22/1.38  # Unit Clause-clause subsumption calls : 20258
% 1.22/1.38  # Rewrite failures with RHS unbound    : 0
% 1.22/1.38  # BW rewrite match attempts            : 1528
% 1.22/1.38  # BW rewrite match successes           : 104
% 1.22/1.38  # Condensation attempts                : 0
% 1.22/1.38  # Condensation successes               : 0
% 1.22/1.38  # Termbank termtop insertions          : 2708285
% 1.22/1.39  
% 1.22/1.39  # -------------------------------------------------
% 1.22/1.39  # User time                : 1.022 s
% 1.22/1.39  # System time              : 0.058 s
% 1.22/1.39  # Total time               : 1.080 s
% 1.22/1.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
