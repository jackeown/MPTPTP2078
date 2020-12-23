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
% DateTime   : Thu Dec  3 11:09:32 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  48 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 215 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_orders_2,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_wellord1(u1_orders_2(X1),X2)
           => ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(t92_orders_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r7_relat_2(X2,X1)
      <=> ( r1_relat_2(X2,X1)
          & r6_relat_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

fof(d5_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_wellord1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2)
            & r1_wellord1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_wellord1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_wellord1(u1_orders_2(X1),X2)
             => ( v6_orders_2(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_orders_2])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & r2_wellord1(u1_orders_2(esk1_0),esk2_0)
    & ( ~ v6_orders_2(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_9,negated_conjecture,
    ( ~ v6_orders_2(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ( ~ v6_orders_2(X10,X9)
        | r7_relat_2(u1_orders_2(X9),X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( ~ r7_relat_2(u1_orders_2(X9),X10)
        | v6_orders_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ( r1_relat_2(X4,X5)
        | ~ r2_wellord1(X4,X5)
        | ~ v1_relat_1(X4) )
      & ( r8_relat_2(X4,X5)
        | ~ r2_wellord1(X4,X5)
        | ~ v1_relat_1(X4) )
      & ( r4_relat_2(X4,X5)
        | ~ r2_wellord1(X4,X5)
        | ~ v1_relat_1(X4) )
      & ( r6_relat_2(X4,X5)
        | ~ r2_wellord1(X4,X5)
        | ~ v1_relat_1(X4) )
      & ( r1_wellord1(X4,X5)
        | ~ r2_wellord1(X4,X5)
        | ~ v1_relat_1(X4) )
      & ( ~ r1_relat_2(X4,X5)
        | ~ r8_relat_2(X4,X5)
        | ~ r4_relat_2(X4,X5)
        | ~ r6_relat_2(X4,X5)
        | ~ r1_wellord1(X4,X5)
        | r2_wellord1(X4,X5)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_wellord1])])])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( ~ v6_orders_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10])])).

cnf(c_0_18,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r7_relat_2(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ r7_relat_2(u1_orders_2(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_16]),c_0_10])])).

cnf(c_0_25,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_wellord1(u1_orders_2(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S028I
% 0.20/0.37  # and selection function SelectNonRROptimalLit.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t40_orders_2, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_wellord1(u1_orders_2(X1),X2)=>(v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_orders_2)).
% 0.20/0.37  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.20/0.37  fof(d11_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_orders_2(X2,X1)<=>r7_relat_2(u1_orders_2(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 0.20/0.37  fof(t92_orders_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r7_relat_2(X2,X1)<=>(r1_relat_2(X2,X1)&r6_relat_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_orders_1)).
% 0.20/0.37  fof(d5_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r2_wellord1(X1,X2)<=>((((r1_relat_2(X1,X2)&r8_relat_2(X1,X2))&r4_relat_2(X1,X2))&r6_relat_2(X1,X2))&r1_wellord1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_wellord1)).
% 0.20/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_wellord1(u1_orders_2(X1),X2)=>(v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))))))), inference(assume_negation,[status(cth)],[t40_orders_2])).
% 0.20/0.37  fof(c_0_7, negated_conjecture, (l1_orders_2(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(r2_wellord1(u1_orders_2(esk1_0),esk2_0)&(~v6_orders_2(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.37  fof(c_0_8, plain, ![X11]:(~l1_orders_2(X11)|m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.20/0.37  cnf(c_0_9, negated_conjecture, (~v6_orders_2(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  fof(c_0_11, plain, ![X9, X10]:((~v6_orders_2(X10,X9)|r7_relat_2(u1_orders_2(X9),X10)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_orders_2(X9))&(~r7_relat_2(u1_orders_2(X9),X10)|v6_orders_2(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_orders_2(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).
% 0.20/0.37  fof(c_0_12, plain, ![X12, X13]:(((r1_relat_2(X13,X12)|~r7_relat_2(X13,X12)|~v1_relat_1(X13))&(r6_relat_2(X13,X12)|~r7_relat_2(X13,X12)|~v1_relat_1(X13)))&(~r1_relat_2(X13,X12)|~r6_relat_2(X13,X12)|r7_relat_2(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_orders_1])])])).
% 0.20/0.37  fof(c_0_13, plain, ![X4, X5]:((((((r1_relat_2(X4,X5)|~r2_wellord1(X4,X5)|~v1_relat_1(X4))&(r8_relat_2(X4,X5)|~r2_wellord1(X4,X5)|~v1_relat_1(X4)))&(r4_relat_2(X4,X5)|~r2_wellord1(X4,X5)|~v1_relat_1(X4)))&(r6_relat_2(X4,X5)|~r2_wellord1(X4,X5)|~v1_relat_1(X4)))&(r1_wellord1(X4,X5)|~r2_wellord1(X4,X5)|~v1_relat_1(X4)))&(~r1_relat_2(X4,X5)|~r8_relat_2(X4,X5)|~r4_relat_2(X4,X5)|~r6_relat_2(X4,X5)|~r1_wellord1(X4,X5)|r2_wellord1(X4,X5)|~v1_relat_1(X4))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_wellord1])])])])).
% 0.20/0.37  fof(c_0_14, plain, ![X6, X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))|v1_relat_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.37  cnf(c_0_15, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_17, negated_conjecture, (~v6_orders_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10])])).
% 0.20/0.37  cnf(c_0_18, plain, (v6_orders_2(X2,X1)|~r7_relat_2(u1_orders_2(X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_19, plain, (r7_relat_2(X1,X2)|~r1_relat_2(X1,X2)|~r6_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_20, plain, (r6_relat_2(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_21, plain, (r1_relat_2(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (~r7_relat_2(u1_orders_2(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_16]), c_0_10])])).
% 0.20/0.37  cnf(c_0_25, plain, (r7_relat_2(X1,X2)|~r2_wellord1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (r2_wellord1(u1_orders_2(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (v1_relat_1(u1_orders_2(esk1_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 29
% 0.20/0.37  # Proof object clause steps            : 16
% 0.20/0.37  # Proof object formula steps           : 13
% 0.20/0.37  # Proof object conjectures             : 12
% 0.20/0.37  # Proof object clause conjectures      : 9
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 10
% 0.20/0.37  # Proof object initial formulas used   : 6
% 0.20/0.37  # Proof object generating inferences   : 5
% 0.20/0.37  # Proof object simplifying inferences  : 9
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 6
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 17
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 17
% 0.20/0.37  # Processed clauses                    : 38
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 38
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 1
% 0.20/0.37  # Generated clauses                    : 7
% 0.20/0.37  # ...of the previous two non-trivial   : 5
% 0.20/0.37  # Contextual simplify-reflections      : 1
% 0.20/0.37  # Paramodulations                      : 7
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 20
% 0.20/0.37  #    Positive orientable unit clauses  : 5
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 13
% 0.20/0.37  # Current number of unprocessed clauses: 1
% 0.20/0.37  # ...number of literals in the above   : 7
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 18
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 82
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 41
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 1
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1383
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.028 s
% 0.20/0.37  # System time              : 0.003 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
