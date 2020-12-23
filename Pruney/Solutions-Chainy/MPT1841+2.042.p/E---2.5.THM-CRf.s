%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 358 expanded)
%              Number of clauses        :   56 ( 155 expanded)
%              Number of leaves         :   15 (  87 expanded)
%              Depth                    :   20
%              Number of atoms          :  211 (1204 expanded)
%              Number of equality atoms :   88 ( 316 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t44_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(cc2_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_subset_1(X2,X1)
           => ~ v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_17,plain,(
    ! [X35,X37] :
      ( ( m1_subset_1(esk4_1(X35),X35)
        | ~ v1_zfmisc_1(X35)
        | v1_xboole_0(X35) )
      & ( X35 = k6_domain_1(X35,esk4_1(X35))
        | ~ v1_zfmisc_1(X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X37,X35)
        | X35 != k6_domain_1(X35,X37)
        | v1_zfmisc_1(X35)
        | v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_18,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk4_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k6_domain_1(X1,esk4_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k6_domain_1(X1,esk4_1(X1)) = k1_tarski(esk4_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | k1_tarski(X2) != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k1_tarski(esk4_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( X1 != k1_tarski(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

cnf(c_0_32,plain,
    ( esk4_1(X1) = X2
    | k1_tarski(X2) != X1
    | ~ v1_zfmisc_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

fof(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk6_0,esk5_0)
    & v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0)
    & v1_zfmisc_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X2)
    | k1_tarski(X1) != X2
    | ~ v1_zfmisc_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_32]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,esk5_0)
    | k1_tarski(X1) != esk5_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_1(X1),esk5_0)
    | v1_xboole_0(X1)
    | X1 != esk5_0
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_35])]),c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( k6_domain_1(esk5_0,esk4_1(esk5_0)) = k1_tarski(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_39]),c_0_38])).

fof(c_0_41,plain,(
    ! [X23,X24] : k2_xboole_0(k1_tarski(X23),X24) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_42,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_43,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_44,plain,(
    ! [X20,X21,X22] :
      ( k1_tarski(X20) != k2_xboole_0(X21,X22)
      | X21 = X22
      | X21 = k1_xboole_0
      | X22 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_zfmisc_1])])).

fof(c_0_45,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_46,negated_conjecture,
    ( k1_tarski(esk4_1(esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_40]),c_0_35])]),c_0_38])).

fof(c_0_47,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X29,X30)
      | v1_xboole_0(X30)
      | r2_hidden(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( X2 = X3
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k1_tarski(X1) != k2_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( X1 = esk4_1(esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_46])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_58,plain,
    ( X2 = X3
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_tarski(X1) != k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k6_domain_1(esk5_0,esk6_0) = k1_tarski(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_53]),c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( k6_domain_1(esk5_0,X1) = esk5_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_54]),c_0_35])]),c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_38])).

cnf(c_0_63,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = X2
    | k1_tarski(X3) != X2
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k1_tarski(esk6_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X2 = X1
    | esk5_0 != X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_35]),c_0_38])).

fof(c_0_69,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_70,negated_conjecture,
    ( X1 = esk5_0
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_67]),c_0_68])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_72,plain,(
    ! [X27] :
      ( m1_subset_1(esk3_1(X27),k1_zfmisc_1(X27))
      & ~ v1_subset_1(esk3_1(X27),X27) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_73,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_74,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | v1_subset_1(X26,X25)
      | ~ v1_xboole_0(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_subset_1])])])])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 = esk5_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( v1_subset_1(k1_tarski(esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_60])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | v1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,plain,
    ( ~ v1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( esk3_1(esk5_0) = esk5_0
    | esk3_1(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( v1_subset_1(esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_65])).

cnf(c_0_82,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk3_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_76]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( esk3_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_84,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:42:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.19/0.45  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.043 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.45  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.45  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 0.19/0.45  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.45  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 0.19/0.45  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.45  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.45  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.45  fof(t44_zfmisc_1, axiom, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.19/0.45  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.45  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.45  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.19/0.45  fof(cc2_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_subset_1(X2,X1))=>~(v1_xboole_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 0.19/0.45  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.45  fof(c_0_15, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.45  fof(c_0_16, plain, ![X33, X34]:(v1_xboole_0(X33)|~m1_subset_1(X34,X33)|k6_domain_1(X33,X34)=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.45  fof(c_0_17, plain, ![X35, X37]:(((m1_subset_1(esk4_1(X35),X35)|~v1_zfmisc_1(X35)|v1_xboole_0(X35))&(X35=k6_domain_1(X35,esk4_1(X35))|~v1_zfmisc_1(X35)|v1_xboole_0(X35)))&(~m1_subset_1(X37,X35)|X35!=k6_domain_1(X35,X37)|v1_zfmisc_1(X35)|v1_xboole_0(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.19/0.45  cnf(c_0_18, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  cnf(c_0_19, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  cnf(c_0_20, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_21, plain, (m1_subset_1(esk4_1(X1),X1)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  fof(c_0_22, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.45  cnf(c_0_23, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_24, plain, (r2_hidden(X1,X2)|X2!=k1_tarski(X1)), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_25, plain, (X1=k6_domain_1(X1,esk4_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_26, plain, (k6_domain_1(X1,esk4_1(X1))=k1_tarski(esk4_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.45  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_28, plain, (X1=X2|k1_tarski(X2)!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.45  cnf(c_0_29, plain, (k1_tarski(esk4_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.45  cnf(c_0_30, plain, (X1!=k1_tarski(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.19/0.45  fof(c_0_31, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.19/0.45  cnf(c_0_32, plain, (esk4_1(X1)=X2|k1_tarski(X2)!=X1|~v1_zfmisc_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.45  fof(c_0_33, negated_conjecture, (~v1_xboole_0(esk5_0)&(m1_subset_1(esk6_0,esk5_0)&(v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0)&v1_zfmisc_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).
% 0.19/0.45  cnf(c_0_34, plain, (m1_subset_1(X1,X2)|k1_tarski(X1)!=X2|~v1_zfmisc_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_32]), c_0_30])).
% 0.19/0.45  cnf(c_0_35, negated_conjecture, (v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,esk5_0)|k1_tarski(X1)!=esk5_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.45  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_1(X1),esk5_0)|v1_xboole_0(X1)|X1!=esk5_0|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 0.19/0.45  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_35])]), c_0_38])).
% 0.19/0.45  cnf(c_0_40, negated_conjecture, (k6_domain_1(esk5_0,esk4_1(esk5_0))=k1_tarski(esk4_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_39]), c_0_38])).
% 0.19/0.45  fof(c_0_41, plain, ![X23, X24]:k2_xboole_0(k1_tarski(X23),X24)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.45  fof(c_0_42, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.45  fof(c_0_43, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.45  fof(c_0_44, plain, ![X20, X21, X22]:(k1_tarski(X20)!=k2_xboole_0(X21,X22)|X21=X22|X21=k1_xboole_0|X22=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_zfmisc_1])])).
% 0.19/0.45  fof(c_0_45, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.45  cnf(c_0_46, negated_conjecture, (k1_tarski(esk4_1(esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_40]), c_0_35])]), c_0_38])).
% 0.19/0.45  fof(c_0_47, plain, ![X29, X30]:(~m1_subset_1(X29,X30)|(v1_xboole_0(X30)|r2_hidden(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.45  cnf(c_0_48, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.45  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.45  cnf(c_0_50, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_51, plain, (X2=X3|X2=k1_xboole_0|X3=k1_xboole_0|k1_tarski(X1)!=k2_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.45  cnf(c_0_52, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.45  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_54, negated_conjecture, (X1=esk4_1(esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_46])).
% 0.19/0.45  cnf(c_0_55, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.45  cnf(c_0_56, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.45  cnf(c_0_57, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_50, c_0_49])).
% 0.19/0.45  cnf(c_0_58, plain, (X2=X3|X3=k1_xboole_0|X2=k1_xboole_0|k1_tarski(X1)!=k5_xboole_0(X2,k4_xboole_0(X3,X2))), inference(rw,[status(thm)],[c_0_51, c_0_49])).
% 0.19/0.45  cnf(c_0_59, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_49])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (k6_domain_1(esk5_0,esk6_0)=k1_tarski(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_53]), c_0_38])).
% 0.19/0.45  cnf(c_0_61, negated_conjecture, (k6_domain_1(esk5_0,X1)=esk5_0|~r2_hidden(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_54]), c_0_35])]), c_0_38])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_38])).
% 0.19/0.45  cnf(c_0_63, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.45  cnf(c_0_64, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X1=X2|k1_tarski(X3)!=X2|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.45  cnf(c_0_65, negated_conjecture, (k1_tarski(esk6_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.19/0.45  cnf(c_0_66, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_29])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|X2=X1|esk5_0!=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (esk5_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_35]), c_0_38])).
% 0.19/0.45  fof(c_0_69, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (X1=esk5_0|X1=k1_xboole_0|~r1_tarski(X1,esk5_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_67]), c_0_68])).
% 0.19/0.45  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.45  fof(c_0_72, plain, ![X27]:(m1_subset_1(esk3_1(X27),k1_zfmisc_1(X27))&~v1_subset_1(esk3_1(X27),X27)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.19/0.45  cnf(c_0_73, negated_conjecture, (v1_subset_1(k6_domain_1(esk5_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  fof(c_0_74, plain, ![X25, X26]:(v1_xboole_0(X25)|(~m1_subset_1(X26,k1_zfmisc_1(X25))|(v1_subset_1(X26,X25)|~v1_xboole_0(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_subset_1])])])])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (X1=k1_xboole_0|X1=esk5_0|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.45  cnf(c_0_76, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (v1_subset_1(k1_tarski(esk6_0),esk5_0)), inference(rw,[status(thm)],[c_0_73, c_0_60])).
% 0.19/0.45  cnf(c_0_78, plain, (v1_xboole_0(X1)|v1_subset_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.45  cnf(c_0_79, plain, (~v1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.45  cnf(c_0_80, negated_conjecture, (esk3_1(esk5_0)=esk5_0|esk3_1(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (v1_subset_1(esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_77, c_0_65])).
% 0.19/0.45  cnf(c_0_82, plain, (v1_xboole_0(X1)|~v1_xboole_0(esk3_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_76]), c_0_79])).
% 0.19/0.45  cnf(c_0_83, negated_conjecture, (esk3_1(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.19/0.45  cnf(c_0_84, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])]), c_0_38]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 86
% 0.19/0.45  # Proof object clause steps            : 56
% 0.19/0.45  # Proof object formula steps           : 30
% 0.19/0.45  # Proof object conjectures             : 26
% 0.19/0.45  # Proof object clause conjectures      : 23
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 21
% 0.19/0.45  # Proof object initial formulas used   : 15
% 0.19/0.45  # Proof object generating inferences   : 28
% 0.19/0.45  # Proof object simplifying inferences  : 31
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 15
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 26
% 0.19/0.45  # Removed in clause preprocessing      : 1
% 0.19/0.45  # Initial clauses in saturation        : 25
% 0.19/0.45  # Processed clauses                    : 473
% 0.19/0.45  # ...of these trivial                  : 8
% 0.19/0.45  # ...subsumed                          : 227
% 0.19/0.45  # ...remaining for further processing  : 238
% 0.19/0.45  # Other redundant clauses eliminated   : 36
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 1
% 0.19/0.45  # Backward-rewritten                   : 14
% 0.19/0.45  # Generated clauses                    : 1798
% 0.19/0.45  # ...of the previous two non-trivial   : 1630
% 0.19/0.45  # Contextual simplify-reflections      : 19
% 0.19/0.45  # Paramodulations                      : 1709
% 0.19/0.45  # Factorizations                       : 3
% 0.19/0.45  # Equation resolutions                 : 86
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 197
% 0.19/0.45  #    Positive orientable unit clauses  : 16
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 12
% 0.19/0.45  #    Non-unit-clauses                  : 169
% 0.19/0.45  # Current number of unprocessed clauses: 1146
% 0.19/0.45  # ...number of literals in the above   : 5913
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 41
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 5466
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 2019
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 222
% 0.19/0.45  # Unit Clause-clause subsumption calls : 134
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 6
% 0.19/0.45  # BW rewrite match successes           : 5
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 21513
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.104 s
% 0.19/0.45  # System time              : 0.010 s
% 0.19/0.45  # Total time               : 0.113 s
% 0.19/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
