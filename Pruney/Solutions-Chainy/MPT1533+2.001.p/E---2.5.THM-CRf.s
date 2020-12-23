%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:14 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  96 expanded)
%              Number of clauses        :   21 (  33 expanded)
%              Number of leaves         :    3 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 568 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_yellow_0,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r2_lattice3(X1,X2,X3)
                  & r1_orders_2(X1,X3,X4) )
               => r2_lattice3(X1,X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( ( r2_lattice3(X1,X2,X3)
                    & r1_orders_2(X1,X3,X4) )
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_yellow_0])).

fof(c_0_4,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r2_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X10)
        | r1_orders_2(X9,X12,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))
        | r2_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | r2_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,esk1_3(X9,X10,X11),X11)
        | r2_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_5,negated_conjecture,
    ( v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & r2_lattice3(esk2_0,esk3_0,esk4_0)
    & r1_orders_2(esk2_0,esk4_0,esk5_0)
    & ~ r2_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ v4_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ r1_orders_2(X5,X6,X7)
      | ~ r1_orders_2(X5,X7,X8)
      | r1_orders_2(X5,X6,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk5_0)
    | m1_subset_1(esk1_3(esk2_0,X1,esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,X2,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_8]),c_0_9]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk5_0)
    | r1_orders_2(esk2_0,esk1_3(esk2_0,X1,esk5_0),X2)
    | ~ r2_hidden(esk1_3(esk2_0,X1,esk5_0),X3)
    | ~ r2_lattice3(esk2_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_9])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,X1,esk5_0),X1)
    | r2_lattice3(esk2_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_8]),c_0_9])])).

cnf(c_0_20,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk5_0)
    | r1_orders_2(esk2_0,esk1_3(esk2_0,X1,esk5_0),X2)
    | ~ r2_lattice3(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk5_0)
    | ~ r1_orders_2(esk2_0,esk1_3(esk2_0,X1,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_8]),c_0_9])]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk5_0)
    | ~ r2_lattice3(esk2_0,X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t11_yellow_0, conjecture, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_lattice3(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r2_lattice3(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_yellow_0)).
% 0.19/0.37  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.19/0.37  fof(t26_orders_2, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 0.19/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_lattice3(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r2_lattice3(X1,X2,X4)))))), inference(assume_negation,[status(cth)],[t11_yellow_0])).
% 0.19/0.37  fof(c_0_4, plain, ![X9, X10, X11, X12]:((~r2_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X10)|r1_orders_2(X9,X12,X11)))|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))|r2_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((r2_hidden(esk1_3(X9,X10,X11),X10)|r2_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~r1_orders_2(X9,esk1_3(X9,X10,X11),X11)|r2_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ((v4_orders_2(esk2_0)&l1_orders_2(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&((r2_lattice3(esk2_0,esk3_0,esk4_0)&r1_orders_2(esk2_0,esk4_0,esk5_0))&~r2_lattice3(esk2_0,esk3_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.19/0.37  fof(c_0_6, plain, ![X5, X6, X7, X8]:(~v4_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~m1_subset_1(X8,u1_struct_0(X5))|(~r1_orders_2(X5,X6,X7)|~r1_orders_2(X5,X7,X8)|r1_orders_2(X5,X6,X8)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).
% 0.19/0.37  cnf(c_0_7, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_9, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_10, plain, (r1_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_12, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (r2_lattice3(esk2_0,X1,esk5_0)|m1_subset_1(esk1_3(esk2_0,X1,esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.19/0.37  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (r1_orders_2(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,X2,esk5_0)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_8]), c_0_9]), c_0_11])])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (r2_lattice3(esk2_0,X1,esk5_0)|r1_orders_2(esk2_0,esk1_3(esk2_0,X1,esk5_0),X2)|~r2_hidden(esk1_3(esk2_0,X1,esk5_0),X3)|~r2_lattice3(esk2_0,X3,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_9])])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_3(esk2_0,X1,esk5_0),X1)|r2_lattice3(esk2_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_8]), c_0_9])])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (r1_orders_2(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r2_lattice3(esk2_0,X1,esk5_0)|r1_orders_2(esk2_0,esk1_3(esk2_0,X1,esk5_0),X2)|~r2_lattice3(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r2_lattice3(esk2_0,X1,esk5_0)|~r1_orders_2(esk2_0,esk1_3(esk2_0,X1,esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_8]), c_0_9])]), c_0_13])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (~r2_lattice3(esk2_0,esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r2_lattice3(esk2_0,X1,esk5_0)|~r2_lattice3(esk2_0,X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_23])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (r2_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 28
% 0.19/0.37  # Proof object clause steps            : 21
% 0.19/0.37  # Proof object formula steps           : 7
% 0.19/0.37  # Proof object conjectures             : 19
% 0.19/0.37  # Proof object clause conjectures      : 16
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 12
% 0.19/0.37  # Proof object initial formulas used   : 3
% 0.19/0.37  # Proof object generating inferences   : 9
% 0.19/0.37  # Proof object simplifying inferences  : 18
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 3
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 12
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 12
% 0.19/0.37  # Processed clauses                    : 46
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 46
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 40
% 0.19/0.37  # ...of the previous two non-trivial   : 37
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 40
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
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
% 0.19/0.37  # Current number of processed clauses  : 34
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 27
% 0.19/0.37  # Current number of unprocessed clauses: 15
% 0.19/0.37  # ...number of literals in the above   : 70
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 12
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 79
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 35
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2316
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
