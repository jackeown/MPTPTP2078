%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:16 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 197 expanded)
%              Number of clauses        :   24 (  66 expanded)
%              Number of leaves         :    6 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 973 expanded)
%              Number of equality atoms :   34 ( 202 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X8 = X10
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) )
      & ( X9 = X11
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_8,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | m1_subset_1(u1_pre_topc(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(X15,u1_pre_topc(X14))
        | u1_pre_topc(X14) = k5_tmap_1(X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( u1_pre_topc(X14) != k5_tmap_1(X14,X15)
        | r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) )
    & ( v3_pre_topc(esk2_0,esk1_0)
      | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_11,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | k6_tmap_1(X12,X13) = g1_pre_topc(u1_struct_0(X12),k5_tmap_1(X12,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_14,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( ~ v3_pre_topc(X6,X5)
        | r2_hidden(X6,u1_pre_topc(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(X6,u1_pre_topc(X5))
        | v3_pre_topc(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0)
    | ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | k5_tmap_1(esk1_0,esk2_0) != u1_pre_topc(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( u1_pre_topc(esk1_0) = X1
    | v3_pre_topc(esk2_0,esk1_0)
    | k6_tmap_1(esk1_0,esk2_0) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

cnf(c_0_29,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0)) = k6_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0)
    | ~ v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15]),c_0_17])])).

cnf(c_0_31,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | k5_tmap_1(esk1_0,esk2_0) != u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15]),c_0_17])])).

cnf(c_0_32,negated_conjecture,
    ( k5_tmap_1(esk1_0,esk2_0) = u1_pre_topc(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != k6_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_32]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n003.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 20:38:12 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 0.16/0.33  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.33  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.33  #
% 0.16/0.33  # Preprocessing time       : 0.027 s
% 0.16/0.33  # Presaturation interreduction done
% 0.16/0.33  
% 0.16/0.33  # Proof found!
% 0.16/0.33  # SZS status Theorem
% 0.16/0.33  # SZS output start CNFRefutation
% 0.16/0.33  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.16/0.33  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.16/0.33  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.16/0.33  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.16/0.33  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 0.16/0.33  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.16/0.33  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.16/0.33  fof(c_0_7, plain, ![X8, X9, X10, X11]:((X8=X10|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))&(X9=X11|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.16/0.33  fof(c_0_8, plain, ![X7]:(~l1_pre_topc(X7)|m1_subset_1(u1_pre_topc(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.16/0.33  fof(c_0_9, plain, ![X14, X15]:((~r2_hidden(X15,u1_pre_topc(X14))|u1_pre_topc(X14)=k5_tmap_1(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(u1_pre_topc(X14)!=k5_tmap_1(X14,X15)|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.16/0.33  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0))&(v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.16/0.33  cnf(c_0_11, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.33  cnf(c_0_12, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.33  fof(c_0_13, plain, ![X12, X13]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|k6_tmap_1(X12,X13)=g1_pre_topc(u1_struct_0(X12),k5_tmap_1(X12,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 0.16/0.33  cnf(c_0_14, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.33  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.33  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.33  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.33  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.33  fof(c_0_19, plain, ![X5, X6]:((~v3_pre_topc(X6,X5)|r2_hidden(X6,u1_pre_topc(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(~r2_hidden(X6,u1_pre_topc(X5))|v3_pre_topc(X6,X5)|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.16/0.33  cnf(c_0_20, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.33  cnf(c_0_21, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.16/0.33  cnf(c_0_22, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.33  cnf(c_0_23, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.16/0.33  cnf(c_0_24, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)|~r2_hidden(esk2_0,u1_pre_topc(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.16/0.33  cnf(c_0_25, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.33  cnf(c_0_26, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.33  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_0,u1_pre_topc(esk1_0))|k5_tmap_1(esk1_0,esk2_0)!=u1_pre_topc(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.16/0.33  cnf(c_0_28, negated_conjecture, (u1_pre_topc(esk1_0)=X1|v3_pre_topc(esk2_0,esk1_0)|k6_tmap_1(esk1_0,esk2_0)!=g1_pre_topc(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.16/0.33  cnf(c_0_29, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),k5_tmap_1(esk1_0,esk2_0))=k6_tmap_1(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.16/0.33  cnf(c_0_30, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)|~v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_15]), c_0_17])])).
% 0.16/0.33  cnf(c_0_31, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)|k5_tmap_1(esk1_0,esk2_0)!=u1_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_15]), c_0_17])])).
% 0.16/0.33  cnf(c_0_32, negated_conjecture, (k5_tmap_1(esk1_0,esk2_0)=u1_pre_topc(esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.16/0.33  cnf(c_0_33, negated_conjecture, (~v3_pre_topc(esk2_0,esk1_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.33  cnf(c_0_34, negated_conjecture, (v3_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])])).
% 0.16/0.33  cnf(c_0_35, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=k6_tmap_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.16/0.33  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_32]), c_0_35]), ['proof']).
% 0.16/0.33  # SZS output end CNFRefutation
% 0.16/0.33  # Proof object total steps             : 37
% 0.16/0.33  # Proof object clause steps            : 24
% 0.16/0.33  # Proof object formula steps           : 13
% 0.16/0.33  # Proof object conjectures             : 19
% 0.16/0.33  # Proof object clause conjectures      : 16
% 0.16/0.33  # Proof object formula conjectures     : 3
% 0.16/0.33  # Proof object initial clauses used    : 13
% 0.16/0.33  # Proof object initial formulas used   : 6
% 0.16/0.33  # Proof object generating inferences   : 8
% 0.16/0.33  # Proof object simplifying inferences  : 27
% 0.16/0.33  # Training examples: 0 positive, 0 negative
% 0.16/0.33  # Parsed axioms                        : 6
% 0.16/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.33  # Initial clauses                      : 14
% 0.16/0.33  # Removed in clause preprocessing      : 0
% 0.16/0.33  # Initial clauses in saturation        : 14
% 0.16/0.33  # Processed clauses                    : 44
% 0.16/0.33  # ...of these trivial                  : 0
% 0.16/0.33  # ...subsumed                          : 2
% 0.16/0.33  # ...remaining for further processing  : 41
% 0.16/0.33  # Other redundant clauses eliminated   : 0
% 0.16/0.33  # Clauses deleted for lack of memory   : 0
% 0.16/0.33  # Backward-subsumed                    : 1
% 0.16/0.33  # Backward-rewritten                   : 8
% 0.16/0.33  # Generated clauses                    : 22
% 0.16/0.33  # ...of the previous two non-trivial   : 19
% 0.16/0.33  # Contextual simplify-reflections      : 1
% 0.16/0.33  # Paramodulations                      : 20
% 0.16/0.33  # Factorizations                       : 0
% 0.16/0.33  # Equation resolutions                 : 2
% 0.16/0.33  # Propositional unsat checks           : 0
% 0.16/0.33  #    Propositional check models        : 0
% 0.16/0.33  #    Propositional check unsatisfiable : 0
% 0.16/0.33  #    Propositional clauses             : 0
% 0.16/0.33  #    Propositional clauses after purity: 0
% 0.16/0.33  #    Propositional unsat core size     : 0
% 0.16/0.33  #    Propositional preprocessing time  : 0.000
% 0.16/0.33  #    Propositional encoding time       : 0.000
% 0.16/0.33  #    Propositional solver time         : 0.000
% 0.16/0.33  #    Success case prop preproc time    : 0.000
% 0.16/0.33  #    Success case prop encoding time   : 0.000
% 0.16/0.33  #    Success case prop solver time     : 0.000
% 0.16/0.33  # Current number of processed clauses  : 18
% 0.16/0.33  #    Positive orientable unit clauses  : 6
% 0.16/0.33  #    Positive unorientable unit clauses: 0
% 0.16/0.33  #    Negative unit clauses             : 2
% 0.16/0.33  #    Non-unit-clauses                  : 10
% 0.16/0.33  # Current number of unprocessed clauses: 2
% 0.16/0.33  # ...number of literals in the above   : 5
% 0.16/0.33  # Current number of archived formulas  : 0
% 0.16/0.33  # Current number of archived clauses   : 23
% 0.16/0.33  # Clause-clause subsumption calls (NU) : 35
% 0.16/0.33  # Rec. Clause-clause subsumption calls : 9
% 0.16/0.33  # Non-unit clause-clause subsumptions  : 3
% 0.16/0.33  # Unit Clause-clause subsumption calls : 4
% 0.16/0.33  # Rewrite failures with RHS unbound    : 0
% 0.16/0.33  # BW rewrite match attempts            : 2
% 0.16/0.33  # BW rewrite match successes           : 2
% 0.16/0.33  # Condensation attempts                : 0
% 0.16/0.33  # Condensation successes               : 0
% 0.16/0.33  # Termbank termtop insertions          : 1739
% 0.16/0.33  
% 0.16/0.33  # -------------------------------------------------
% 0.16/0.33  # User time                : 0.031 s
% 0.16/0.33  # System time              : 0.001 s
% 0.16/0.33  # Total time               : 0.032 s
% 0.16/0.33  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
