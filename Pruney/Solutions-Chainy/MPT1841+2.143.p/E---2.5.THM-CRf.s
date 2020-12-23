%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:12 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of clauses        :   32 (  36 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 226 expanded)
%              Number of equality atoms :   46 (  49 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(c_0_14,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X9
        | X12 = X10
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( esk2_3(X14,X15,X16) != X14
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( esk2_3(X14,X15,X16) != X15
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X16)
        | esk2_3(X14,X15,X16) = X14
        | esk2_3(X14,X15,X16) = X15
        | X16 = k2_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X28,X29] :
      ( v1_xboole_0(X28)
      | ~ m1_subset_1(X29,X28)
      | k6_domain_1(X28,X29) = k1_tarski(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_20,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | m1_subset_1(k6_domain_1(X25,X26),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk4_0,esk3_0)
    & v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0)
    & v1_zfmisc_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_18])).

fof(c_0_32,plain,(
    ! [X32,X33] :
      ( v1_xboole_0(X32)
      | v1_xboole_0(X33)
      | ~ v1_zfmisc_1(X33)
      | ~ r1_tarski(X32,X33)
      | X32 = X33 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_35,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k6_domain_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_29])).

fof(c_0_38,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | ~ v1_subset_1(k2_struct_0(X24),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

fof(c_0_39,plain,(
    ! [X23] :
      ( ~ l1_struct_0(X23)
      | k2_struct_0(X23) = u1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_40,plain,(
    ! [X27] :
      ( ~ l1_orders_2(X27)
      | l1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_41,plain,(
    ! [X30] :
      ( v1_orders_2(k2_yellow_1(X30))
      & l1_orders_2(k2_yellow_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k6_domain_1(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,k6_domain_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X31] :
      ( u1_struct_0(k2_yellow_1(X31)) = X31
      & u1_orders_2(k2_yellow_1(X31)) = k1_yellow_1(X31) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k6_domain_1(esk3_0,esk4_0) = esk3_0
    | v1_xboole_0(k6_domain_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(k6_domain_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( k6_domain_1(esk3_0,esk4_0) = esk3_0 ),
    inference(sr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:50:05 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.14/0.36  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.14/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.36  #
% 0.14/0.36  # Preprocessing time       : 0.028 s
% 0.14/0.36  
% 0.14/0.36  # Proof found!
% 0.14/0.36  # SZS status Theorem
% 0.14/0.36  # SZS output start CNFRefutation
% 0.14/0.36  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.36  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.14/0.36  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.36  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.14/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.36  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.14/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.36  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.14/0.36  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.14/0.36  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.36  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.14/0.36  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.14/0.36  fof(c_0_14, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(X12=X9|X12=X10)|X11!=k2_tarski(X9,X10))&((X13!=X9|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))))&(((esk2_3(X14,X15,X16)!=X14|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15))&(esk2_3(X14,X15,X16)!=X15|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15)))&(r2_hidden(esk2_3(X14,X15,X16),X16)|(esk2_3(X14,X15,X16)=X14|esk2_3(X14,X15,X16)=X15)|X16=k2_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.36  fof(c_0_15, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.36  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.14/0.36  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.36  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.36  fof(c_0_19, plain, ![X28, X29]:(v1_xboole_0(X28)|~m1_subset_1(X29,X28)|k6_domain_1(X28,X29)=k1_tarski(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.36  fof(c_0_20, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.36  fof(c_0_21, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|m1_subset_1(k6_domain_1(X25,X26),k1_zfmisc_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.14/0.36  fof(c_0_22, negated_conjecture, (~v1_xboole_0(esk3_0)&(m1_subset_1(esk4_0,esk3_0)&(v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0)&v1_zfmisc_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.14/0.36  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.36  cnf(c_0_24, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.36  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.36  fof(c_0_26, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.36  cnf(c_0_27, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.36  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.36  cnf(c_0_29, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.36  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X3,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.36  cnf(c_0_31, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_18])).
% 0.14/0.36  fof(c_0_32, plain, ![X32, X33]:(v1_xboole_0(X32)|(v1_xboole_0(X33)|~v1_zfmisc_1(X33)|(~r1_tarski(X32,X33)|X32=X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.14/0.36  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.36  cnf(c_0_34, negated_conjecture, (m1_subset_1(k6_domain_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.14/0.36  fof(c_0_35, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.36  cnf(c_0_36, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[c_0_30])).
% 0.14/0.36  cnf(c_0_37, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k6_domain_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_29])).
% 0.14/0.36  fof(c_0_38, plain, ![X24]:(~l1_struct_0(X24)|~v1_subset_1(k2_struct_0(X24),u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.14/0.36  fof(c_0_39, plain, ![X23]:(~l1_struct_0(X23)|k2_struct_0(X23)=u1_struct_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.14/0.36  fof(c_0_40, plain, ![X27]:(~l1_orders_2(X27)|l1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.36  fof(c_0_41, plain, ![X30]:(v1_orders_2(k2_yellow_1(X30))&l1_orders_2(k2_yellow_1(X30))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.14/0.36  cnf(c_0_42, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.36  cnf(c_0_43, negated_conjecture, (r1_tarski(k6_domain_1(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.36  cnf(c_0_44, negated_conjecture, (v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.36  cnf(c_0_45, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.36  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,k6_domain_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.36  cnf(c_0_47, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.36  cnf(c_0_48, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.36  fof(c_0_49, plain, ![X31]:(u1_struct_0(k2_yellow_1(X31))=X31&u1_orders_2(k2_yellow_1(X31))=k1_yellow_1(X31)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.14/0.36  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.36  cnf(c_0_51, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.36  cnf(c_0_52, negated_conjecture, (k6_domain_1(esk3_0,esk4_0)=esk3_0|v1_xboole_0(k6_domain_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), c_0_29])).
% 0.14/0.36  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(k6_domain_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.36  cnf(c_0_54, plain, (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.36  cnf(c_0_55, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.36  cnf(c_0_56, plain, (l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.14/0.36  cnf(c_0_57, negated_conjecture, (v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.36  cnf(c_0_58, negated_conjecture, (k6_domain_1(esk3_0,esk4_0)=esk3_0), inference(sr,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.36  cnf(c_0_59, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.14/0.36  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_59]), ['proof']).
% 0.14/0.36  # SZS output end CNFRefutation
% 0.14/0.36  # Proof object total steps             : 61
% 0.14/0.36  # Proof object clause steps            : 32
% 0.14/0.36  # Proof object formula steps           : 29
% 0.14/0.36  # Proof object conjectures             : 15
% 0.14/0.36  # Proof object clause conjectures      : 12
% 0.14/0.36  # Proof object formula conjectures     : 3
% 0.14/0.36  # Proof object initial clauses used    : 17
% 0.14/0.36  # Proof object initial formulas used   : 14
% 0.14/0.36  # Proof object generating inferences   : 10
% 0.14/0.36  # Proof object simplifying inferences  : 14
% 0.14/0.36  # Training examples: 0 positive, 0 negative
% 0.14/0.36  # Parsed axioms                        : 14
% 0.14/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.36  # Initial clauses                      : 26
% 0.14/0.36  # Removed in clause preprocessing      : 3
% 0.14/0.36  # Initial clauses in saturation        : 23
% 0.14/0.36  # Processed clauses                    : 44
% 0.14/0.36  # ...of these trivial                  : 0
% 0.14/0.36  # ...subsumed                          : 3
% 0.14/0.36  # ...remaining for further processing  : 41
% 0.14/0.36  # Other redundant clauses eliminated   : 12
% 0.14/0.36  # Clauses deleted for lack of memory   : 0
% 0.14/0.36  # Backward-subsumed                    : 0
% 0.14/0.36  # Backward-rewritten                   : 7
% 0.14/0.36  # Generated clauses                    : 112
% 0.14/0.36  # ...of the previous two non-trivial   : 93
% 0.14/0.36  # Contextual simplify-reflections      : 0
% 0.14/0.36  # Paramodulations                      : 75
% 0.14/0.36  # Factorizations                       : 20
% 0.14/0.36  # Equation resolutions                 : 16
% 0.14/0.36  # Propositional unsat checks           : 0
% 0.14/0.36  #    Propositional check models        : 0
% 0.14/0.36  #    Propositional check unsatisfiable : 0
% 0.14/0.36  #    Propositional clauses             : 0
% 0.14/0.36  #    Propositional clauses after purity: 0
% 0.14/0.36  #    Propositional unsat core size     : 0
% 0.14/0.36  #    Propositional preprocessing time  : 0.000
% 0.14/0.36  #    Propositional encoding time       : 0.000
% 0.14/0.36  #    Propositional solver time         : 0.000
% 0.14/0.36  #    Success case prop preproc time    : 0.000
% 0.14/0.36  #    Success case prop encoding time   : 0.000
% 0.14/0.36  #    Success case prop solver time     : 0.000
% 0.14/0.36  # Current number of processed clauses  : 31
% 0.14/0.36  #    Positive orientable unit clauses  : 8
% 0.14/0.36  #    Positive unorientable unit clauses: 0
% 0.14/0.36  #    Negative unit clauses             : 3
% 0.14/0.36  #    Non-unit-clauses                  : 20
% 0.14/0.36  # Current number of unprocessed clauses: 66
% 0.14/0.36  # ...number of literals in the above   : 273
% 0.14/0.36  # Current number of archived formulas  : 0
% 0.14/0.36  # Current number of archived clauses   : 11
% 0.14/0.36  # Clause-clause subsumption calls (NU) : 84
% 0.14/0.36  # Rec. Clause-clause subsumption calls : 45
% 0.14/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.36  # Unit Clause-clause subsumption calls : 33
% 0.14/0.36  # Rewrite failures with RHS unbound    : 0
% 0.14/0.36  # BW rewrite match attempts            : 2
% 0.14/0.36  # BW rewrite match successes           : 1
% 0.14/0.36  # Condensation attempts                : 0
% 0.14/0.36  # Condensation successes               : 0
% 0.14/0.36  # Termbank termtop insertions          : 2395
% 0.14/0.36  
% 0.14/0.36  # -------------------------------------------------
% 0.14/0.36  # User time                : 0.031 s
% 0.14/0.36  # System time              : 0.004 s
% 0.14/0.36  # Total time               : 0.035 s
% 0.14/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
