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
% DateTime   : Thu Dec  3 11:16:11 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 170 expanded)
%              Number of clauses        :   21 (  52 expanded)
%              Number of leaves         :    4 (  42 expanded)
%              Depth                    :    5
%              Number of atoms          :  130 (1066 expanded)
%              Number of equality atoms :   13 ( 214 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( k6_waybel_0(X1,X2) = k6_waybel_0(X1,X3)
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( k6_waybel_0(X1,X2) = k6_waybel_0(X1,X3)
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_waybel_0])).

fof(c_0_5,plain,(
    ! [X4,X5,X6] :
      ( ( ~ r3_orders_2(X4,X5,X6)
        | r1_orders_2(X4,X5,X6)
        | v2_struct_0(X4)
        | ~ v3_orders_2(X4)
        | ~ l1_orders_2(X4)
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ m1_subset_1(X6,u1_struct_0(X4)) )
      & ( ~ r1_orders_2(X4,X5,X6)
        | r3_orders_2(X4,X5,X6)
        | v2_struct_0(X4)
        | ~ v3_orders_2(X4)
        | ~ l1_orders_2(X4)
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k6_waybel_0(esk1_0,esk2_0) = k6_waybel_0(esk1_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( v2_struct_0(X7)
      | ~ v3_orders_2(X7)
      | ~ l1_orders_2(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | r3_orders_2(X7,X8,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_8,plain,(
    ! [X10,X11,X12] :
      ( ~ v5_orders_2(X10)
      | ~ l1_orders_2(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ r1_orders_2(X10,X11,X12)
      | ~ r1_orders_2(X10,X12,X11)
      | X11 = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_9,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_16,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_17,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r3_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11]),c_0_12])]),c_0_13]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r3_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_15]),c_0_11]),c_0_12])]),c_0_13]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_10]),c_0_11]),c_0_12])]),c_0_13]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_11]),c_0_12])]),c_0_13]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk2_0
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_18]),c_0_11])]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk3_0
    | ~ r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_18]),c_0_11])]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_10])]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_15])]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( k6_waybel_0(esk1_0,esk2_0) = k6_waybel_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(t20_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k6_waybel_0(X1,X2)=k6_waybel_0(X1,X3)=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_waybel_0)).
% 0.19/0.37  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.19/0.37  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.19/0.37  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k6_waybel_0(X1,X2)=k6_waybel_0(X1,X3)=>X2=X3))))), inference(assume_negation,[status(cth)],[t20_waybel_0])).
% 0.19/0.37  fof(c_0_5, plain, ![X4, X5, X6]:((~r3_orders_2(X4,X5,X6)|r1_orders_2(X4,X5,X6)|(v2_struct_0(X4)|~v3_orders_2(X4)|~l1_orders_2(X4)|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X4))))&(~r1_orders_2(X4,X5,X6)|r3_orders_2(X4,X5,X6)|(v2_struct_0(X4)|~v3_orders_2(X4)|~l1_orders_2(X4)|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X4))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(k6_waybel_0(esk1_0,esk2_0)=k6_waybel_0(esk1_0,esk3_0)&esk2_0!=esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X7, X8, X9]:(v2_struct_0(X7)|~v3_orders_2(X7)|~l1_orders_2(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|r3_orders_2(X7,X8,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.19/0.37  fof(c_0_8, plain, ![X10, X11, X12]:(~v5_orders_2(X10)|~l1_orders_2(X10)|(~m1_subset_1(X11,u1_struct_0(X10))|(~m1_subset_1(X12,u1_struct_0(X10))|(~r1_orders_2(X10,X11,X12)|~r1_orders_2(X10,X12,X11)|X11=X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.19/0.37  cnf(c_0_9, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (v3_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_14, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_16, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.37  cnf(c_0_17, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r1_orders_2(esk1_0,X1,esk2_0)|~r3_orders_2(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (r3_orders_2(esk1_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_11]), c_0_12])]), c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (r1_orders_2(esk1_0,X1,esk3_0)|~r3_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_15]), c_0_11]), c_0_12])]), c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r3_orders_2(esk1_0,X1,esk2_0)|~r1_orders_2(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_10]), c_0_11]), c_0_12])]), c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r3_orders_2(esk1_0,X1,esk3_0)|~r1_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_15]), c_0_11]), c_0_12])]), c_0_13]), ['final']).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (X1=esk2_0|~r1_orders_2(esk1_0,esk2_0,X1)|~r1_orders_2(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_10]), c_0_18]), c_0_11])]), ['final']).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (X1=esk3_0|~r1_orders_2(esk1_0,esk3_0,X1)|~r1_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_18]), c_0_11])]), ['final']).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_10])]), ['final']).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r1_orders_2(esk1_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_15])]), ['final']).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (k6_waybel_0(esk1_0,esk2_0)=k6_waybel_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 30
% 0.19/0.37  # Proof object clause steps            : 21
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 20
% 0.19/0.37  # Proof object clause conjectures      : 17
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 12
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 9
% 0.19/0.37  # Proof object simplifying inferences  : 30
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 12
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 12
% 0.19/0.37  # Processed clauses                    : 34
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 33
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 12
% 0.19/0.37  # ...of the previous two non-trivial   : 10
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 12
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
% 0.19/0.37  # Current number of processed clauses  : 21
% 0.19/0.37  #    Positive orientable unit clauses  : 8
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 11
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 12
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 17
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 11
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1471
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.026 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
