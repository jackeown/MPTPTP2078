%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:31 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 477 expanded)
%              Number of clauses        :   25 ( 165 expanded)
%              Number of leaves         :    3 ( 110 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 (4154 expanded)
%              Number of equality atoms :   13 ( 102 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_orders_2,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( ( r2_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X3,X4) )
                      | ( r1_orders_2(X1,X2,X3)
                        & r2_orders_2(X1,X3,X4) ) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(t29_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r2_orders_2(X1,X2,X3)
                      & r2_orders_2(X1,X3,X4) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( ( r2_orders_2(X1,X2,X3)
                          & r1_orders_2(X1,X3,X4) )
                        | ( r1_orders_2(X1,X2,X3)
                          & r2_orders_2(X1,X3,X4) ) )
                     => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_orders_2])).

fof(c_0_4,plain,(
    ! [X8,X9,X10,X11] :
      ( ~ v4_orders_2(X8)
      | ~ v5_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ r2_orders_2(X8,X9,X10)
      | ~ r2_orders_2(X8,X10,X11)
      | r2_orders_2(X8,X9,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_orders_2])])])).

fof(c_0_5,negated_conjecture,
    ( v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r2_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | r2_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ~ r2_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
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

cnf(c_0_7,plain,
    ( r2_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r2_orders_2(esk1_0,X2,esk4_0)
    | ~ r2_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk3_0
    | r2_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_11])])).

cnf(c_0_18,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r2_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_20,negated_conjecture,
    ( esk2_0 = esk3_0
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_16])])).

cnf(c_0_21,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_8]),c_0_11])])).

cnf(c_0_22,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 = esk3_0
    | ~ r2_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13])])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_13])])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk2_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_25]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_26]),c_0_28])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:19:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S021N
% 0.13/0.35  # and selection function PSelectAllCondOptimalLit.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.013 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t32_orders_2, conjecture, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))|(r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4)))=>r2_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_orders_2)).
% 0.13/0.35  fof(t29_orders_2, axiom, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4))=>r2_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_orders_2)).
% 0.13/0.35  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 0.13/0.35  fof(c_0_3, negated_conjecture, ~(![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))|(r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4)))=>r2_orders_2(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t32_orders_2])).
% 0.13/0.35  fof(c_0_4, plain, ![X8, X9, X10, X11]:(~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|(~m1_subset_1(X11,u1_struct_0(X8))|(~r2_orders_2(X8,X9,X10)|~r2_orders_2(X8,X10,X11)|r2_orders_2(X8,X9,X11)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_orders_2])])])).
% 0.13/0.35  fof(c_0_5, negated_conjecture, (((v4_orders_2(esk1_0)&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(m1_subset_1(esk4_0,u1_struct_0(esk1_0))&((((r1_orders_2(esk1_0,esk2_0,esk3_0)|r2_orders_2(esk1_0,esk2_0,esk3_0))&(r2_orders_2(esk1_0,esk3_0,esk4_0)|r2_orders_2(esk1_0,esk2_0,esk3_0)))&((r1_orders_2(esk1_0,esk2_0,esk3_0)|r1_orders_2(esk1_0,esk3_0,esk4_0))&(r2_orders_2(esk1_0,esk3_0,esk4_0)|r1_orders_2(esk1_0,esk3_0,esk4_0))))&~r2_orders_2(esk1_0,esk2_0,esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.13/0.35  fof(c_0_6, plain, ![X5, X6, X7]:(((r1_orders_2(X5,X6,X7)|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))&(X6!=X7|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5)))&(~r1_orders_2(X5,X6,X7)|X6=X7|r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.13/0.35  cnf(c_0_7, plain, (r2_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r2_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.35  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_9, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_10, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_12, plain, (X2=X3|r2_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.35  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_14, negated_conjecture, (~r2_orders_2(esk1_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_15, negated_conjecture, (r2_orders_2(esk1_0,X1,esk4_0)|~r2_orders_2(esk1_0,X2,esk4_0)|~r2_orders_2(esk1_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11])])).
% 0.13/0.35  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_17, negated_conjecture, (X1=esk3_0|r2_orders_2(esk1_0,X1,esk3_0)|~r1_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_11])])).
% 0.13/0.35  cnf(c_0_18, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,esk3_0)|r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_19, negated_conjecture, (~r2_orders_2(esk1_0,X1,esk4_0)|~r2_orders_2(esk1_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.13/0.35  cnf(c_0_20, negated_conjecture, (esk2_0=esk3_0|r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_16])])).
% 0.13/0.35  cnf(c_0_21, negated_conjecture, (X1=esk4_0|r2_orders_2(esk1_0,X1,esk4_0)|~r1_orders_2(esk1_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_8]), c_0_11])])).
% 0.13/0.35  cnf(c_0_22, negated_conjecture, (r2_orders_2(esk1_0,esk3_0,esk4_0)|r1_orders_2(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_23, negated_conjecture, (esk2_0=esk3_0|~r2_orders_2(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_13])])).
% 0.13/0.35  cnf(c_0_24, negated_conjecture, (esk4_0=esk3_0|r2_orders_2(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_13])])).
% 0.13/0.35  cnf(c_0_25, negated_conjecture, (esk4_0=esk3_0|esk2_0=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.35  cnf(c_0_26, negated_conjecture, (esk2_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_25]), c_0_20])).
% 0.13/0.35  cnf(c_0_27, negated_conjecture, (~r2_orders_2(esk1_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_14, c_0_26])).
% 0.13/0.35  cnf(c_0_28, negated_conjecture, (esk4_0=esk3_0), inference(sr,[status(thm)],[c_0_24, c_0_27])).
% 0.13/0.35  cnf(c_0_29, negated_conjecture, (r2_orders_2(esk1_0,esk3_0,esk4_0)|r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.35  cnf(c_0_30, negated_conjecture, (~r2_orders_2(esk1_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.35  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_26]), c_0_28])]), c_0_30]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 32
% 0.13/0.35  # Proof object clause steps            : 25
% 0.13/0.35  # Proof object formula steps           : 7
% 0.13/0.35  # Proof object conjectures             : 26
% 0.13/0.35  # Proof object clause conjectures      : 23
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 12
% 0.13/0.35  # Proof object initial formulas used   : 3
% 0.13/0.35  # Proof object generating inferences   : 9
% 0.13/0.35  # Proof object simplifying inferences  : 24
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 3
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 15
% 0.13/0.35  # Removed in clause preprocessing      : 0
% 0.13/0.35  # Initial clauses in saturation        : 15
% 0.13/0.35  # Processed clauses                    : 56
% 0.13/0.35  # ...of these trivial                  : 2
% 0.13/0.35  # ...subsumed                          : 3
% 0.13/0.35  # ...remaining for further processing  : 50
% 0.13/0.35  # Other redundant clauses eliminated   : 1
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 0
% 0.13/0.35  # Backward-rewritten                   : 16
% 0.13/0.35  # Generated clauses                    : 38
% 0.13/0.35  # ...of the previous two non-trivial   : 44
% 0.13/0.35  # Contextual simplify-reflections      : 1
% 0.13/0.35  # Paramodulations                      : 35
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 1
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 16
% 0.13/0.35  #    Positive orientable unit clauses  : 7
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 1
% 0.13/0.35  #    Non-unit-clauses                  : 8
% 0.13/0.35  # Current number of unprocessed clauses: 13
% 0.13/0.35  # ...number of literals in the above   : 63
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 33
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 95
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 18
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.35  # Unit Clause-clause subsumption calls : 12
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.35  # BW rewrite match attempts            : 2
% 0.13/0.35  # BW rewrite match successes           : 2
% 0.13/0.35  # Condensation attempts                : 0
% 0.13/0.35  # Condensation successes               : 0
% 0.13/0.35  # Termbank termtop insertions          : 1881
% 0.13/0.35  
% 0.13/0.35  # -------------------------------------------------
% 0.13/0.35  # User time                : 0.013 s
% 0.13/0.35  # System time              : 0.004 s
% 0.13/0.35  # Total time               : 0.017 s
% 0.13/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
