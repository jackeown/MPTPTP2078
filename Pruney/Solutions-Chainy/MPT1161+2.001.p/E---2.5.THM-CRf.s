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
% DateTime   : Thu Dec  3 11:09:57 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   20 (  49 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :  116 ( 334 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ r2_hidden(X2,k3_orders_2(X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ r2_hidden(X2,k3_orders_2(X1,X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_orders_2])).

fof(c_0_4,plain,(
    ! [X5,X6,X7] :
      ( ( r1_orders_2(X5,X6,X7)
        | ~ r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( X6 != X7
        | ~ r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | X6 = X7
        | r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11] :
      ( ( r2_orders_2(X8,X9,X10)
        | ~ r2_hidden(X9,k3_orders_2(X8,X11,X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_hidden(X9,X11)
        | ~ r2_hidden(X9,k3_orders_2(X8,X11,X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ r2_orders_2(X8,X9,X10)
        | ~ r2_hidden(X9,X11)
        | r2_hidden(X9,k3_orders_2(X8,X11,X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & r2_hidden(esk2_0,k3_orders_2(esk1_0,esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

cnf(c_0_7,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk2_0,k3_orders_2(esk1_0,esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.036 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t62_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(r2_hidden(X2,k3_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_orders_2)).
% 0.19/0.38  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.19/0.38  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.19/0.38  fof(c_0_3, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(r2_hidden(X2,k3_orders_2(X1,X3,X2))))))), inference(assume_negation,[status(cth)],[t62_orders_2])).
% 0.19/0.38  fof(c_0_4, plain, ![X5, X6, X7]:(((r1_orders_2(X5,X6,X7)|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))&(X6!=X7|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5)))&(~r1_orders_2(X5,X6,X7)|X6=X7|r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.19/0.38  fof(c_0_5, plain, ![X8, X9, X10, X11]:(((r2_orders_2(X8,X9,X10)|~r2_hidden(X9,k3_orders_2(X8,X11,X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))&(r2_hidden(X9,X11)|~r2_hidden(X9,k3_orders_2(X8,X11,X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8))))&(~r2_orders_2(X8,X9,X10)|~r2_hidden(X9,X11)|r2_hidden(X9,k3_orders_2(X8,X11,X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.19/0.38  fof(c_0_6, negated_conjecture, (((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v4_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&r2_hidden(esk2_0,k3_orders_2(esk1_0,esk3_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).
% 0.19/0.38  cnf(c_0_7, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.38  cnf(c_0_8, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_9, negated_conjecture, (r2_hidden(esk2_0,k3_orders_2(esk1_0,esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_10, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_12, negated_conjecture, (v3_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_17, plain, (~r2_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (r2_orders_2(esk1_0,esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_14]), c_0_15])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 20
% 0.19/0.38  # Proof object clause steps            : 13
% 0.19/0.38  # Proof object formula steps           : 7
% 0.19/0.38  # Proof object conjectures             : 13
% 0.19/0.38  # Proof object clause conjectures      : 10
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 3
% 0.19/0.38  # Proof object generating inferences   : 2
% 0.19/0.38  # Proof object simplifying inferences  : 12
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 3
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 14
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 14
% 0.19/0.38  # Processed clauses                    : 31
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 31
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 6
% 0.19/0.38  # ...of the previous two non-trivial   : 4
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 5
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 16
% 0.19/0.38  #    Positive orientable unit clauses  : 9
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 6
% 0.19/0.38  # Current number of unprocessed clauses: 1
% 0.19/0.38  # ...number of literals in the above   : 11
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 14
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 81
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 1
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 1527
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
