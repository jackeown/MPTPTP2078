%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:20 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   28 (  43 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  119 ( 252 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t92_orders_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r7_relat_2(X2,X1)
      <=> ( r1_relat_2(X2,X1)
          & r6_relat_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

fof(d8_orders_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r3_orders_1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t135_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r3_orders_1(u1_orders_2(X1),X2)
           => ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_orders_2)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(c_0_6,plain,(
    ! [X12,X13] :
      ( ( r1_relat_2(X13,X12)
        | ~ r7_relat_2(X13,X12)
        | ~ v1_relat_1(X13) )
      & ( r6_relat_2(X13,X12)
        | ~ r7_relat_2(X13,X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_relat_2(X13,X12)
        | ~ r6_relat_2(X13,X12)
        | r7_relat_2(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_orders_1])])])).

fof(c_0_7,plain,(
    ! [X9,X10] :
      ( ( r1_relat_2(X9,X10)
        | ~ r3_orders_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( r8_relat_2(X9,X10)
        | ~ r3_orders_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( r4_relat_2(X9,X10)
        | ~ r3_orders_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( r6_relat_2(X9,X10)
        | ~ r3_orders_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_relat_2(X9,X10)
        | ~ r8_relat_2(X9,X10)
        | ~ r4_relat_2(X9,X10)
        | ~ r6_relat_2(X9,X10)
        | r3_orders_1(X9,X10)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_orders_1])])])])).

fof(c_0_8,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_9,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r3_orders_1(u1_orders_2(X1),X2)
             => ( v6_orders_2(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t135_orders_2])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ( ~ v6_orders_2(X8,X7)
        | r7_relat_2(u1_orders_2(X7),X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( ~ r7_relat_2(u1_orders_2(X7),X8)
        | v6_orders_2(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_12,plain,
    ( r7_relat_2(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r6_relat_2(X1,X2)
    | ~ r3_orders_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r1_relat_2(X1,X2)
    | ~ r3_orders_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & r3_orders_1(u1_orders_2(esk1_0),esk2_0)
    & ( ~ v6_orders_2(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_18,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r7_relat_2(X1,X2)
    | ~ r3_orders_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ v6_orders_2(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v6_orders_2(X1,X2)
    | ~ r3_orders_1(u1_orders_2(X2),X1)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r3_orders_1(u1_orders_2(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v6_orders_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_24]),c_0_25])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.31  % Computer   : n017.cluster.edu
% 0.09/0.31  % Model      : x86_64 x86_64
% 0.09/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.31  % Memory     : 8042.1875MB
% 0.09/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.31  % CPULimit   : 60
% 0.09/0.31  % WCLimit    : 600
% 0.09/0.31  % DateTime   : Tue Dec  1 18:40:31 EST 2020
% 0.09/0.31  % CPUTime    : 
% 0.09/0.31  # Version: 2.5pre002
% 0.09/0.31  # No SInE strategy applied
% 0.09/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.33  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.33  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.33  #
% 0.16/0.33  # Preprocessing time       : 0.017 s
% 0.16/0.33  # Presaturation interreduction done
% 0.16/0.33  
% 0.16/0.33  # Proof found!
% 0.16/0.33  # SZS status Theorem
% 0.16/0.33  # SZS output start CNFRefutation
% 0.16/0.33  fof(t92_orders_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r7_relat_2(X2,X1)<=>(r1_relat_2(X2,X1)&r6_relat_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_orders_1)).
% 0.16/0.33  fof(d8_orders_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r3_orders_1(X1,X2)<=>(((r1_relat_2(X1,X2)&r8_relat_2(X1,X2))&r4_relat_2(X1,X2))&r6_relat_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_orders_1)).
% 0.16/0.33  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.16/0.33  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.16/0.33  fof(t135_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r3_orders_1(u1_orders_2(X1),X2)=>(v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_orders_2)).
% 0.16/0.33  fof(d11_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_orders_2(X2,X1)<=>r7_relat_2(u1_orders_2(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 0.16/0.33  fof(c_0_6, plain, ![X12, X13]:(((r1_relat_2(X13,X12)|~r7_relat_2(X13,X12)|~v1_relat_1(X13))&(r6_relat_2(X13,X12)|~r7_relat_2(X13,X12)|~v1_relat_1(X13)))&(~r1_relat_2(X13,X12)|~r6_relat_2(X13,X12)|r7_relat_2(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_orders_1])])])).
% 0.16/0.33  fof(c_0_7, plain, ![X9, X10]:(((((r1_relat_2(X9,X10)|~r3_orders_1(X9,X10)|~v1_relat_1(X9))&(r8_relat_2(X9,X10)|~r3_orders_1(X9,X10)|~v1_relat_1(X9)))&(r4_relat_2(X9,X10)|~r3_orders_1(X9,X10)|~v1_relat_1(X9)))&(r6_relat_2(X9,X10)|~r3_orders_1(X9,X10)|~v1_relat_1(X9)))&(~r1_relat_2(X9,X10)|~r8_relat_2(X9,X10)|~r4_relat_2(X9,X10)|~r6_relat_2(X9,X10)|r3_orders_1(X9,X10)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_orders_1])])])])).
% 0.16/0.33  fof(c_0_8, plain, ![X4, X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|v1_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.16/0.33  fof(c_0_9, plain, ![X11]:(~l1_orders_2(X11)|m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.16/0.33  fof(c_0_10, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r3_orders_1(u1_orders_2(X1),X2)=>(v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))))))), inference(assume_negation,[status(cth)],[t135_orders_2])).
% 0.16/0.33  fof(c_0_11, plain, ![X7, X8]:((~v6_orders_2(X8,X7)|r7_relat_2(u1_orders_2(X7),X8)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_orders_2(X7))&(~r7_relat_2(u1_orders_2(X7),X8)|v6_orders_2(X8,X7)|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|~l1_orders_2(X7))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).
% 0.16/0.33  cnf(c_0_12, plain, (r7_relat_2(X1,X2)|~r1_relat_2(X1,X2)|~r6_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.33  cnf(c_0_13, plain, (r6_relat_2(X1,X2)|~r3_orders_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.33  cnf(c_0_14, plain, (r1_relat_2(X1,X2)|~r3_orders_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.33  cnf(c_0_15, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.33  cnf(c_0_16, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.33  fof(c_0_17, negated_conjecture, (((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v4_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(r3_orders_1(u1_orders_2(esk1_0),esk2_0)&(~v6_orders_2(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.16/0.33  cnf(c_0_18, plain, (v6_orders_2(X2,X1)|~r7_relat_2(u1_orders_2(X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.33  cnf(c_0_19, plain, (r7_relat_2(X1,X2)|~r3_orders_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.16/0.33  cnf(c_0_20, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.16/0.33  cnf(c_0_21, negated_conjecture, (~v6_orders_2(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.33  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.33  cnf(c_0_23, plain, (v6_orders_2(X1,X2)|~r3_orders_1(u1_orders_2(X2),X1)|~l1_orders_2(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.16/0.33  cnf(c_0_24, negated_conjecture, (r3_orders_1(u1_orders_2(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.33  cnf(c_0_25, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.33  cnf(c_0_26, negated_conjecture, (~v6_orders_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])])).
% 0.16/0.33  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_24]), c_0_25])]), c_0_26]), ['proof']).
% 0.16/0.33  # SZS output end CNFRefutation
% 0.16/0.33  # Proof object total steps             : 28
% 0.16/0.33  # Proof object clause steps            : 15
% 0.16/0.33  # Proof object formula steps           : 13
% 0.16/0.33  # Proof object conjectures             : 9
% 0.16/0.33  # Proof object clause conjectures      : 6
% 0.16/0.33  # Proof object formula conjectures     : 3
% 0.16/0.33  # Proof object initial clauses used    : 10
% 0.16/0.33  # Proof object initial formulas used   : 6
% 0.16/0.33  # Proof object generating inferences   : 4
% 0.16/0.33  # Proof object simplifying inferences  : 8
% 0.16/0.33  # Training examples: 0 positive, 0 negative
% 0.16/0.33  # Parsed axioms                        : 6
% 0.16/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.33  # Initial clauses                      : 20
% 0.16/0.33  # Removed in clause preprocessing      : 0
% 0.16/0.33  # Initial clauses in saturation        : 20
% 0.16/0.33  # Processed clauses                    : 43
% 0.16/0.33  # ...of these trivial                  : 0
% 0.16/0.33  # ...subsumed                          : 0
% 0.16/0.33  # ...remaining for further processing  : 43
% 0.16/0.33  # Other redundant clauses eliminated   : 0
% 0.16/0.33  # Clauses deleted for lack of memory   : 0
% 0.16/0.33  # Backward-subsumed                    : 0
% 0.16/0.33  # Backward-rewritten                   : 0
% 0.16/0.33  # Generated clauses                    : 7
% 0.16/0.33  # ...of the previous two non-trivial   : 3
% 0.16/0.33  # Contextual simplify-reflections      : 2
% 0.16/0.33  # Paramodulations                      : 7
% 0.16/0.33  # Factorizations                       : 0
% 0.16/0.33  # Equation resolutions                 : 0
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
% 0.16/0.33  # Current number of processed clauses  : 23
% 0.16/0.33  #    Positive orientable unit clauses  : 6
% 0.16/0.33  #    Positive unorientable unit clauses: 0
% 0.16/0.33  #    Negative unit clauses             : 2
% 0.16/0.33  #    Non-unit-clauses                  : 15
% 0.16/0.33  # Current number of unprocessed clauses: 0
% 0.16/0.33  # ...number of literals in the above   : 0
% 0.16/0.33  # Current number of archived formulas  : 0
% 0.16/0.33  # Current number of archived clauses   : 20
% 0.16/0.33  # Clause-clause subsumption calls (NU) : 57
% 0.16/0.33  # Rec. Clause-clause subsumption calls : 40
% 0.16/0.33  # Non-unit clause-clause subsumptions  : 2
% 0.16/0.33  # Unit Clause-clause subsumption calls : 0
% 0.16/0.33  # Rewrite failures with RHS unbound    : 0
% 0.16/0.33  # BW rewrite match attempts            : 0
% 0.16/0.33  # BW rewrite match successes           : 0
% 0.16/0.33  # Condensation attempts                : 0
% 0.16/0.33  # Condensation successes               : 0
% 0.16/0.33  # Termbank termtop insertions          : 1514
% 0.16/0.33  
% 0.16/0.33  # -------------------------------------------------
% 0.16/0.33  # User time                : 0.015 s
% 0.16/0.33  # System time              : 0.005 s
% 0.16/0.33  # Total time               : 0.020 s
% 0.16/0.33  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
