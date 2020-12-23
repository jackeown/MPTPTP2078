%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:22 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 129 expanded)
%              Number of clauses        :   20 (  41 expanded)
%              Number of leaves         :    3 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :  119 ( 881 expanded)
%              Number of equality atoms :   16 (  29 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_lattices(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattices(X1,X2,X3)
                      & r1_lattices(X1,X3,X4) )
                   => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_lattices)).

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(d5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ( v5_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => k1_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k1_lattices(X1,X2,X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattices)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_lattices(X1)
          & l2_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r1_lattices(X1,X2,X3)
                        & r1_lattices(X1,X3,X4) )
                     => r1_lattices(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_lattices])).

fof(c_0_4,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r1_lattices(X5,X6,X7)
        | k1_lattices(X5,X6,X7) = X7
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l2_lattices(X5) )
      & ( k1_lattices(X5,X6,X7) != X7
        | r1_lattices(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | v2_struct_0(X5)
        | ~ l2_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v5_lattices(esk4_0)
    & l2_lattices(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & r1_lattices(esk4_0,esk5_0,esk6_0)
    & r1_lattices(esk4_0,esk6_0,esk7_0)
    & ~ r1_lattices(esk4_0,esk5_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ v5_lattices(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X11,u1_struct_0(X8))
        | k1_lattices(X8,X9,k1_lattices(X8,X10,X11)) = k1_lattices(X8,k1_lattices(X8,X9,X10),X11)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( m1_subset_1(esk1_1(X8),u1_struct_0(X8))
        | v5_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( m1_subset_1(esk2_1(X8),u1_struct_0(X8))
        | v5_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( m1_subset_1(esk3_1(X8),u1_struct_0(X8))
        | v5_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( k1_lattices(X8,esk1_1(X8),k1_lattices(X8,esk2_1(X8),esk3_1(X8))) != k1_lattices(X8,k1_lattices(X8,esk1_1(X8),esk2_1(X8)),esk3_1(X8))
        | v5_lattices(X8)
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_lattices])])])])])])).

cnf(c_0_7,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l2_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( k1_lattices(X1,X2,k1_lattices(X1,X3,X4)) = k1_lattices(X1,k1_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ v5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v5_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( k1_lattices(esk4_0,X1,esk6_0) = esk6_0
    | ~ r1_lattices(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_lattices(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( k1_lattices(esk4_0,X1,esk7_0) = esk7_0
    | ~ r1_lattices(esk4_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_11]),c_0_9])]),c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r1_lattices(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_lattices(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattices(esk4_0,X1,esk7_0)
    | k1_lattices(esk4_0,X1,esk7_0) != esk7_0
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_11]),c_0_9])]),c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( k1_lattices(esk4_0,k1_lattices(esk4_0,X1,X2),esk7_0) = k1_lattices(esk4_0,X1,k1_lattices(esk4_0,X2,esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_14]),c_0_9])]),c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( k1_lattices(esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_24,negated_conjecture,
    ( k1_lattices(esk4_0,esk6_0,esk7_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_8])])).

cnf(c_0_25,negated_conjecture,
    ( k1_lattices(esk4_0,esk5_0,esk7_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),c_0_8]),c_0_17])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t25_lattices, conjecture, ![X1]:(((~(v2_struct_0(X1))&v5_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X4))=>r1_lattices(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_lattices)).
% 0.13/0.37  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.13/0.37  fof(d5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>(v5_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k1_lattices(X1,X2,k1_lattices(X1,X3,X4))=k1_lattices(X1,k1_lattices(X1,X2,X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_lattices)).
% 0.13/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v5_lattices(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattices(X1,X2,X3)&r1_lattices(X1,X3,X4))=>r1_lattices(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t25_lattices])).
% 0.13/0.37  fof(c_0_4, plain, ![X5, X6, X7]:((~r1_lattices(X5,X6,X7)|k1_lattices(X5,X6,X7)=X7|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))&(k1_lattices(X5,X6,X7)!=X7|r1_lattices(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|(v2_struct_0(X5)|~l2_lattices(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.13/0.37  fof(c_0_5, negated_conjecture, (((~v2_struct_0(esk4_0)&v5_lattices(esk4_0))&l2_lattices(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&((r1_lattices(esk4_0,esk5_0,esk6_0)&r1_lattices(esk4_0,esk6_0,esk7_0))&~r1_lattices(esk4_0,esk5_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X8, X9, X10, X11]:((~v5_lattices(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|(~m1_subset_1(X11,u1_struct_0(X8))|k1_lattices(X8,X9,k1_lattices(X8,X10,X11))=k1_lattices(X8,k1_lattices(X8,X9,X10),X11))))|(v2_struct_0(X8)|~l2_lattices(X8)))&((m1_subset_1(esk1_1(X8),u1_struct_0(X8))|v5_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8)))&((m1_subset_1(esk2_1(X8),u1_struct_0(X8))|v5_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8)))&((m1_subset_1(esk3_1(X8),u1_struct_0(X8))|v5_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8)))&(k1_lattices(X8,esk1_1(X8),k1_lattices(X8,esk2_1(X8),esk3_1(X8)))!=k1_lattices(X8,k1_lattices(X8,esk1_1(X8),esk2_1(X8)),esk3_1(X8))|v5_lattices(X8)|(v2_struct_0(X8)|~l2_lattices(X8))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_lattices])])])])])])).
% 0.13/0.37  cnf(c_0_7, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (l2_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_12, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_13, plain, (k1_lattices(X1,X2,k1_lattices(X1,X3,X4))=k1_lattices(X1,k1_lattices(X1,X2,X3),X4)|v2_struct_0(X1)|~v5_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (v5_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (k1_lattices(esk4_0,X1,esk6_0)=esk6_0|~r1_lattices(esk4_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])]), c_0_10])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (r1_lattices(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (k1_lattices(esk4_0,X1,esk7_0)=esk7_0|~r1_lattices(esk4_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_11]), c_0_9])]), c_0_10])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r1_lattices(esk4_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (~r1_lattices(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r1_lattices(esk4_0,X1,esk7_0)|k1_lattices(esk4_0,X1,esk7_0)!=esk7_0|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_11]), c_0_9])]), c_0_10])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (k1_lattices(esk4_0,k1_lattices(esk4_0,X1,X2),esk7_0)=k1_lattices(esk4_0,X1,k1_lattices(esk4_0,X2,esk7_0))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_11]), c_0_14]), c_0_9])]), c_0_10])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (k1_lattices(esk4_0,esk5_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k1_lattices(esk4_0,esk6_0,esk7_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_8])])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (k1_lattices(esk4_0,esk5_0,esk7_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_17])])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24]), c_0_8]), c_0_17])]), c_0_25]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 27
% 0.13/0.37  # Proof object clause steps            : 20
% 0.13/0.37  # Proof object formula steps           : 7
% 0.13/0.37  # Proof object conjectures             : 20
% 0.13/0.37  # Proof object clause conjectures      : 17
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 12
% 0.13/0.37  # Proof object initial formulas used   : 3
% 0.13/0.37  # Proof object generating inferences   : 8
% 0.13/0.37  # Proof object simplifying inferences  : 25
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 3
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 16
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 16
% 0.13/0.37  # Processed clauses                    : 42
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 42
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 22
% 0.13/0.37  # ...of the previous two non-trivial   : 14
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 22
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 26
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 14
% 0.13/0.37  # Current number of unprocessed clauses: 2
% 0.13/0.37  # ...number of literals in the above   : 6
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 16
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 37
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 15
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 7
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1914
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
