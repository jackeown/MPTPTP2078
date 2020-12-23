%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:20 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  43 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   84 ( 129 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(t15_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
              & v1_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_6,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_tex_2(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != u1_struct_0(X9)
        | v1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | v1_tex_2(X9,X8)
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X8) )
      & ( esk2_2(X8,X9) = u1_struct_0(X9)
        | v1_tex_2(X9,X8)
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ v1_subset_1(esk2_2(X8,X9),u1_struct_0(X8))
        | v1_tex_2(X9,X8)
        | ~ m1_pre_topc(X9,X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ~ ( u1_struct_0(X2) = u1_struct_0(X1)
                & v1_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_tex_2])).

fof(c_0_8,plain,(
    ! [X12,X13] :
      ( ( ~ v1_subset_1(X13,X12)
        | X13 != X12
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) )
      & ( X13 = X12
        | v1_subset_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_9,plain,(
    ! [X6] :
      ( m1_subset_1(esk1_1(X6),k1_zfmisc_1(X6))
      & ~ v1_subset_1(esk1_1(X6),X6) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

cnf(c_0_10,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & u1_struct_0(esk4_0) = u1_struct_0(esk3_0)
    & v1_tex_2(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( ~ v1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X5] : ~ v1_subset_1(k2_subset_1(X5),X5) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_16,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_17,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( esk1_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_20,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v1_tex_2(esk4_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:11:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.19/0.36  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.027 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.19/0.36  fof(t15_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 0.19/0.36  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.36  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.19/0.36  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.19/0.36  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.36  fof(c_0_6, plain, ![X8, X9, X10]:((~v1_tex_2(X9,X8)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|(X10!=u1_struct_0(X9)|v1_subset_1(X10,u1_struct_0(X8))))|~m1_pre_topc(X9,X8)|~l1_pre_topc(X8))&((m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))|v1_tex_2(X9,X8)|~m1_pre_topc(X9,X8)|~l1_pre_topc(X8))&((esk2_2(X8,X9)=u1_struct_0(X9)|v1_tex_2(X9,X8)|~m1_pre_topc(X9,X8)|~l1_pre_topc(X8))&(~v1_subset_1(esk2_2(X8,X9),u1_struct_0(X8))|v1_tex_2(X9,X8)|~m1_pre_topc(X9,X8)|~l1_pre_topc(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.19/0.36  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>~((u1_struct_0(X2)=u1_struct_0(X1)&v1_tex_2(X2,X1)))))), inference(assume_negation,[status(cth)],[t15_tex_2])).
% 0.19/0.36  fof(c_0_8, plain, ![X12, X13]:((~v1_subset_1(X13,X12)|X13!=X12|~m1_subset_1(X13,k1_zfmisc_1(X12)))&(X13=X12|v1_subset_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.36  fof(c_0_9, plain, ![X6]:(m1_subset_1(esk1_1(X6),k1_zfmisc_1(X6))&~v1_subset_1(esk1_1(X6),X6)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.19/0.36  cnf(c_0_10, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_pre_topc(esk4_0,esk3_0)&(u1_struct_0(esk4_0)=u1_struct_0(esk3_0)&v1_tex_2(esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.36  cnf(c_0_12, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.36  cnf(c_0_13, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_14, plain, (~v1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  fof(c_0_15, plain, ![X5]:~v1_subset_1(k2_subset_1(X5),X5), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.19/0.36  fof(c_0_16, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.36  cnf(c_0_17, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_19, plain, (esk1_1(X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.19/0.36  cnf(c_0_20, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.36  cnf(c_0_21, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.36  cnf(c_0_22, negated_conjecture, (v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(X1))|~v1_tex_2(esk4_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.36  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_13, c_0_19])).
% 0.19/0.36  cnf(c_0_24, negated_conjecture, (v1_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_27, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.36  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 29
% 0.19/0.36  # Proof object clause steps            : 16
% 0.19/0.36  # Proof object formula steps           : 13
% 0.19/0.36  # Proof object conjectures             : 9
% 0.19/0.36  # Proof object clause conjectures      : 6
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 10
% 0.19/0.36  # Proof object initial formulas used   : 6
% 0.19/0.36  # Proof object generating inferences   : 4
% 0.19/0.36  # Proof object simplifying inferences  : 8
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 6
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 14
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 13
% 0.19/0.37  # Processed clauses                    : 33
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 31
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 14
% 0.19/0.37  # ...of the previous two non-trivial   : 13
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 12
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
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
% 0.19/0.37  # Current number of processed clauses  : 16
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 9
% 0.19/0.37  # Current number of unprocessed clauses: 4
% 0.19/0.37  # ...number of literals in the above   : 15
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 15
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 27
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 10
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 4
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1213
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
