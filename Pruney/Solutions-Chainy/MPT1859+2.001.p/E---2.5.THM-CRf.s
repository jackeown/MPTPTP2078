%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:34 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 148 expanded)
%              Number of clauses        :   18 (  49 expanded)
%              Number of leaves         :    3 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 770 expanded)
%              Number of equality atoms :    9 ( 110 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(t27_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( X2 = u1_struct_0(X1)
           => ( v2_tex_2(X2,X1)
            <=> v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v2_tex_2(X7,X5)
        | v1_tdlat_3(X6)
        | X7 != u1_struct_0(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ v1_tdlat_3(X6)
        | v2_tex_2(X7,X5)
        | X7 != u1_struct_0(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( X2 = u1_struct_0(X1)
             => ( v2_tex_2(X2,X1)
              <=> v1_tdlat_3(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_tex_2])).

cnf(c_0_5,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & esk2_0 = u1_struct_0(esk1_0)
    & ( ~ v2_tex_2(esk2_0,esk1_0)
      | ~ v1_tdlat_3(esk1_0) )
    & ( v2_tex_2(esk2_0,esk1_0)
      | v1_tdlat_3(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( esk2_0 = u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | m1_pre_topc(X4,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v2_tex_2(u1_struct_0(X1),esk1_0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_14,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | v1_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( v1_tdlat_3(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0)
    | ~ v1_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_8]),c_0_8]),c_0_15]),c_0_9])]),c_0_10]),c_0_16])).

cnf(c_0_20,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(u1_struct_0(X1),X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_tdlat_3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_22,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_tex_2(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_8]),c_0_21]),c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_8]),c_0_15]),c_0_9])]),c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.20/0.37  # and selection function SelectNewComplexAHPNS.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 0.20/0.37  fof(t27_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(X2=u1_struct_0(X1)=>(v2_tex_2(X2,X1)<=>v1_tdlat_3(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 0.20/0.37  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.37  fof(c_0_3, plain, ![X5, X6, X7]:((~v2_tex_2(X7,X5)|v1_tdlat_3(X6)|X7!=u1_struct_0(X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X6)|~m1_pre_topc(X6,X5))|(v2_struct_0(X5)|~l1_pre_topc(X5)))&(~v1_tdlat_3(X6)|v2_tex_2(X7,X5)|X7!=u1_struct_0(X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))|(v2_struct_0(X6)|~m1_pre_topc(X6,X5))|(v2_struct_0(X5)|~l1_pre_topc(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.20/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(X2=u1_struct_0(X1)=>(v2_tex_2(X2,X1)<=>v1_tdlat_3(X1)))))), inference(assume_negation,[status(cth)],[t27_tex_2])).
% 0.20/0.37  cnf(c_0_5, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.37  fof(c_0_6, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(esk2_0=u1_struct_0(esk1_0)&((~v2_tex_2(esk2_0,esk1_0)|~v1_tdlat_3(esk1_0))&(v2_tex_2(esk2_0,esk1_0)|v1_tdlat_3(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.20/0.37  cnf(c_0_7, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(er,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_8, negated_conjecture, (esk2_0=u1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_9, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_10, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  fof(c_0_11, plain, ![X4]:(~l1_pre_topc(X4)|m1_pre_topc(X4,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (v2_tex_2(u1_struct_0(X1),esk1_0)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])]), c_0_10])).
% 0.20/0.37  cnf(c_0_14, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_12, c_0_8])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (v2_tex_2(esk2_0,esk1_0)|v1_tdlat_3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_17, plain, (v1_tdlat_3(X3)|v2_struct_0(X3)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|X1!=u1_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (~v2_tex_2(esk2_0,esk1_0)|~v1_tdlat_3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (v2_tex_2(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_8]), c_0_8]), c_0_15]), c_0_9])]), c_0_10]), c_0_16])).
% 0.20/0.37  cnf(c_0_20, plain, (v1_tdlat_3(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_tex_2(u1_struct_0(X1),X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (~v1_tdlat_3(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (v2_struct_0(X1)|~v2_tex_2(esk2_0,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_8]), c_0_21]), c_0_10])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (~m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_8]), c_0_15]), c_0_9])]), c_0_10])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_14]), c_0_9])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 25
% 0.20/0.37  # Proof object clause steps            : 18
% 0.20/0.37  # Proof object formula steps           : 7
% 0.20/0.37  # Proof object conjectures             : 16
% 0.20/0.37  # Proof object clause conjectures      : 13
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 9
% 0.20/0.37  # Proof object initial formulas used   : 3
% 0.20/0.37  # Proof object generating inferences   : 5
% 0.20/0.37  # Proof object simplifying inferences  : 24
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 3
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 9
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 9
% 0.20/0.37  # Processed clauses                    : 17
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 1
% 0.20/0.37  # ...remaining for further processing  : 16
% 0.20/0.37  # Other redundant clauses eliminated   : 2
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 1
% 0.20/0.37  # Backward-rewritten                   : 1
% 0.20/0.37  # Generated clauses                    : 8
% 0.20/0.37  # ...of the previous two non-trivial   : 8
% 0.20/0.37  # Contextual simplify-reflections      : 1
% 0.20/0.37  # Paramodulations                      : 6
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 2
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
% 0.20/0.37  # Current number of processed clauses  : 12
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 3
% 0.20/0.37  #    Non-unit-clauses                  : 5
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 2
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 35
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 1
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 858
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.027 s
% 0.20/0.37  # System time              : 0.003 s
% 0.20/0.37  # Total time               : 0.030 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
