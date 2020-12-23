%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:24 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 158 expanded)
%              Number of clauses        :   28 (  61 expanded)
%              Number of leaves         :    8 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  143 ( 664 expanded)
%              Number of equality atoms :   18 ( 125 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(rc1_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

fof(t39_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_0)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | ~ v1_xboole_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_9,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | m1_subset_1(u1_orders_2(X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X15)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_10,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_xboole_0(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_xboole_0(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_11,plain,(
    ! [X4] :
      ( ( m1_subset_1(esk1_1(X4),k1_zfmisc_1(X4))
        | v1_xboole_0(X4) )
      & ( ~ v1_xboole_0(esk1_1(X4))
        | v1_xboole_0(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
              & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_yellow_0])).

cnf(c_0_18,plain,
    ( ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,u1_orders_2(X1))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

cnf(c_0_19,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [final]).

fof(c_0_20,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r1_orders_2(X12,X13,X14)
        | r2_hidden(k4_tarski(X13,X14),u1_orders_2(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),u1_orders_2(X12))
        | r1_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( v2_struct_0(X18)
      | ~ v3_orders_2(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | r1_orders_2(X18,X19,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ( k1_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != esk3_0
      | k2_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != esk3_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_23,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | ~ m1_subset_1(X17,X16)
      | k6_domain_1(X16,X17) = k1_tarski(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_24,plain,
    ( ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,u1_orders_2(X1))
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_32,plain,
    ( ~ r1_orders_2(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k1_tarski(esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29]),c_0_27])]),
    [final]).

cnf(c_0_36,plain,
    ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))),u1_orders_2(X1)) = k1_tarski(u1_orders_2(X1))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_13]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k1_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != esk3_0
    | k2_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k1_tarski(esk3_0) ),
    inference(sr,[status(thm)],[c_0_34,c_0_35]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))),u1_orders_2(esk2_0)) = k1_tarski(u1_orders_2(esk2_0))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k1_yellow_0(esk2_0,k1_tarski(esk3_0)) != esk3_0
    | k2_yellow_0(esk2_0,k1_tarski(esk3_0)) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38]),
    [final]).

cnf(c_0_41,plain,
    ( k6_domain_1(k1_zfmisc_1(X1),esk1_1(X1)) = k1_tarski(esk1_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15]),
    [final]).

cnf(c_0_42,plain,
    ( v1_xboole_0(u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13]),
    [final]).

cnf(c_0_43,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.14/0.38  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.14/0.38  fof(rc1_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_subset_1)).
% 0.14/0.38  fof(t39_yellow_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_0)).
% 0.14/0.38  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.14/0.38  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.14/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.38  fof(c_0_8, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|~v1_xboole_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.38  fof(c_0_9, plain, ![X15]:(~l1_orders_2(X15)|m1_subset_1(u1_orders_2(X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X15))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.14/0.38  fof(c_0_10, plain, ![X9, X10, X11]:(~v1_xboole_0(X9)|(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X4]:((m1_subset_1(esk1_1(X4),k1_zfmisc_1(X4))|v1_xboole_0(X4))&(~v1_xboole_0(esk1_1(X4))|v1_xboole_0(X4))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).
% 0.14/0.38  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_13, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_14, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_15, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_16, plain, (v1_xboole_0(X1)|~v1_xboole_0(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))=X2&k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))=X2)))), inference(assume_negation,[status(cth)],[t39_yellow_0])).
% 0.14/0.38  cnf(c_0_18, plain, (~l1_orders_2(X1)|~r2_hidden(X2,u1_orders_2(X1))|~v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.14/0.38  cnf(c_0_19, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), ['final']).
% 0.14/0.38  fof(c_0_20, plain, ![X12, X13, X14]:((~r1_orders_2(X12,X13,X14)|r2_hidden(k4_tarski(X13,X14),u1_orders_2(X12))|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|~l1_orders_2(X12))&(~r2_hidden(k4_tarski(X13,X14),u1_orders_2(X12))|r1_orders_2(X12,X13,X14)|~m1_subset_1(X14,u1_struct_0(X12))|~m1_subset_1(X13,u1_struct_0(X12))|~l1_orders_2(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.14/0.38  fof(c_0_21, plain, ![X18, X19]:(v2_struct_0(X18)|~v3_orders_2(X18)|~l1_orders_2(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|r1_orders_2(X18,X19,X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.14/0.38  fof(c_0_22, negated_conjecture, ((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(k1_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=esk3_0|k2_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.14/0.38  fof(c_0_23, plain, ![X16, X17]:(v1_xboole_0(X16)|~m1_subset_1(X17,X16)|k6_domain_1(X16,X17)=k1_tarski(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.38  cnf(c_0_24, plain, (~l1_orders_2(X1)|~r2_hidden(X2,u1_orders_2(X1))|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.14/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_31, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_32, plain, (~r1_orders_2(X1,X2,X3)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k1_tarski(esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29]), c_0_27])]), ['final']).
% 0.14/0.38  cnf(c_0_36, plain, (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))),u1_orders_2(X1))=k1_tarski(u1_orders_2(X1))|v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_31, c_0_13]), ['final']).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (k1_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=esk3_0|k2_yellow_0(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k1_tarski(esk3_0)), inference(sr,[status(thm)],[c_0_34, c_0_35]), ['final']).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))),u1_orders_2(esk2_0))=k1_tarski(u1_orders_2(esk2_0))|v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_36, c_0_29]), ['final']).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k1_yellow_0(esk2_0,k1_tarski(esk3_0))!=esk3_0|k2_yellow_0(esk2_0,k1_tarski(esk3_0))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38]), ['final']).
% 0.14/0.38  cnf(c_0_41, plain, (k6_domain_1(k1_zfmisc_1(X1),esk1_1(X1))=k1_tarski(esk1_1(X1))|v1_xboole_0(k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_42, plain, (v1_xboole_0(u1_orders_2(X1))|~l1_orders_2(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_14, c_0_13]), ['final']).
% 0.14/0.38  cnf(c_0_43, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 45
% 0.14/0.38  # Proof object clause steps            : 28
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 15
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 11
% 0.14/0.38  # Proof object simplifying inferences  : 11
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 15
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 15
% 0.14/0.38  # Processed clauses                    : 44
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 44
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 15
% 0.14/0.38  # ...of the previous two non-trivial   : 14
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 14
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 26
% 0.14/0.38  #    Positive orientable unit clauses  : 6
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 18
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 18
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 15
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 6
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 4
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1698
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.026 s
% 0.14/0.38  # System time              : 0.007 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
