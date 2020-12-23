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
% DateTime   : Thu Dec  3 11:15:20 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  88 expanded)
%              Number of clauses        :   21 (  28 expanded)
%              Number of leaves         :    2 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :  133 ( 932 expanded)
%              Number of equality atoms :   14 ( 105 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k1_yellow_0(X1,X3)
            <=> ( r2_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_yellow_0)).

fof(d12_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r2_lattice3(X1,X2,X3)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_lattice3)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( X2 = k1_yellow_0(X1,X3)
              <=> ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_yellow_0])).

fof(c_0_3,negated_conjecture,(
    ! [X16] :
      ( ~ v2_struct_0(esk4_0)
      & v5_orders_2(esk4_0)
      & v3_lattice3(esk4_0)
      & l1_orders_2(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & ( m1_subset_1(esk7_0,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0)
        | esk5_0 != k1_yellow_0(esk4_0,esk6_0) )
      & ( r2_lattice3(esk4_0,esk6_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0)
        | esk5_0 != k1_yellow_0(esk4_0,esk6_0) )
      & ( ~ r1_orders_2(esk4_0,esk5_0,esk7_0)
        | ~ r2_lattice3(esk4_0,esk6_0,esk5_0)
        | esk5_0 != k1_yellow_0(esk4_0,esk6_0) )
      & ( r2_lattice3(esk4_0,esk6_0,esk5_0)
        | esk5_0 = k1_yellow_0(esk4_0,esk6_0) )
      & ( ~ m1_subset_1(X16,u1_struct_0(esk4_0))
        | ~ r2_lattice3(esk4_0,esk6_0,X16)
        | r1_orders_2(esk4_0,esk5_0,X16)
        | esk5_0 = k1_yellow_0(esk4_0,esk6_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).

fof(c_0_4,plain,(
    ! [X5,X6,X8,X10] :
      ( ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_lattice3(X5,X6,esk1_2(X5,X6))
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_lattice3(X5,X6,X8)
        | r1_orders_2(X5,esk1_2(X5,X6),X8)
        | ~ v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk3_2(X5,X10),u1_struct_0(X5))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r2_lattice3(X5,esk2_1(X5),X10)
        | v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( r2_lattice3(X5,esk2_1(X5),esk3_2(X5,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r2_lattice3(X5,esk2_1(X5),X10)
        | v3_lattice3(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X10,esk3_2(X5,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r2_lattice3(X5,esk2_1(X5),X10)
        | v3_lattice3(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_5,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,X1)
    | esk5_0 = k1_yellow_0(esk4_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( v3_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_9,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk6_0) = esk5_0
    | r1_orders_2(esk4_0,esk5_0,esk1_2(esk4_0,esk6_0))
    | ~ m1_subset_1(esk1_2(esk4_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,esk1_2(X1,X2),esk1_2(X1,X3))
    | ~ r2_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( k1_yellow_0(esk4_0,esk6_0) = esk5_0
    | r1_orders_2(esk4_0,esk5_0,esk1_2(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_10]),c_0_7]),c_0_8])]),
    [final]).

cnf(c_0_15,plain,
    ( r1_orders_2(X1,esk1_2(X1,X2),esk1_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_6]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk5_0)
    | ~ r2_lattice3(esk4_0,X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_13]),c_0_7]),c_0_8])]),
    [final]).

cnf(c_0_17,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_18,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_19,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk7_0)
    | ~ r2_lattice3(esk4_0,esk6_0,esk5_0)
    | esk5_0 != k1_yellow_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    | ~ r2_lattice3(esk4_0,esk6_0,esk5_0)
    | esk5_0 != k1_yellow_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( r2_lattice3(esk4_0,esk6_0,esk5_0)
    | esk5_0 = k1_yellow_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,esk7_0)
    | ~ r2_lattice3(esk4_0,esk6_0,esk5_0)
    | esk5_0 != k1_yellow_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 19:44:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.37  # No SInE strategy applied
% 0.14/0.37  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.22/0.39  # and selection function SelectNewComplexAHP.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.027 s
% 0.22/0.39  
% 0.22/0.39  # No proof found!
% 0.22/0.39  # SZS status CounterSatisfiable
% 0.22/0.39  # SZS output start Saturation
% 0.22/0.39  fof(t32_yellow_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k1_yellow_0(X1,X3)<=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_yellow_0)).
% 0.22/0.39  fof(d12_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v3_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_lattice3)).
% 0.22/0.39  fof(c_0_2, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v3_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k1_yellow_0(X1,X3)<=>(r2_lattice3(X1,X3,X2)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X3,X4)=>r1_orders_2(X1,X2,X4)))))))), inference(assume_negation,[status(cth)],[t32_yellow_0])).
% 0.22/0.39  fof(c_0_3, negated_conjecture, ![X16]:((((~v2_struct_0(esk4_0)&v5_orders_2(esk4_0))&v3_lattice3(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(((m1_subset_1(esk7_0,u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0!=k1_yellow_0(esk4_0,esk6_0))&((r2_lattice3(esk4_0,esk6_0,esk7_0)|~r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0!=k1_yellow_0(esk4_0,esk6_0))&(~r1_orders_2(esk4_0,esk5_0,esk7_0)|~r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0!=k1_yellow_0(esk4_0,esk6_0))))&((r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0=k1_yellow_0(esk4_0,esk6_0))&(~m1_subset_1(X16,u1_struct_0(esk4_0))|(~r2_lattice3(esk4_0,esk6_0,X16)|r1_orders_2(esk4_0,esk5_0,X16))|esk5_0=k1_yellow_0(esk4_0,esk6_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).
% 0.22/0.39  fof(c_0_4, plain, ![X5, X6, X8, X10]:((((m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))|~v3_lattice3(X5)|~l1_orders_2(X5))&(r2_lattice3(X5,X6,esk1_2(X5,X6))|~v3_lattice3(X5)|~l1_orders_2(X5)))&(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_lattice3(X5,X6,X8)|r1_orders_2(X5,esk1_2(X5,X6),X8))|~v3_lattice3(X5)|~l1_orders_2(X5)))&((m1_subset_1(esk3_2(X5,X10),u1_struct_0(X5))|(~m1_subset_1(X10,u1_struct_0(X5))|~r2_lattice3(X5,esk2_1(X5),X10))|v3_lattice3(X5)|~l1_orders_2(X5))&((r2_lattice3(X5,esk2_1(X5),esk3_2(X5,X10))|(~m1_subset_1(X10,u1_struct_0(X5))|~r2_lattice3(X5,esk2_1(X5),X10))|v3_lattice3(X5)|~l1_orders_2(X5))&(~r1_orders_2(X5,X10,esk3_2(X5,X10))|(~m1_subset_1(X10,u1_struct_0(X5))|~r2_lattice3(X5,esk2_1(X5),X10))|v3_lattice3(X5)|~l1_orders_2(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).
% 0.22/0.39  cnf(c_0_5, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,X1)|esk5_0=k1_yellow_0(esk4_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_6, plain, (r2_lattice3(X1,X2,esk1_2(X1,X2))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.22/0.39  cnf(c_0_7, negated_conjecture, (v3_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_8, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_9, plain, (r1_orders_2(X2,esk1_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~v3_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.22/0.39  cnf(c_0_10, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.22/0.39  cnf(c_0_11, negated_conjecture, (k1_yellow_0(esk4_0,esk6_0)=esk5_0|r1_orders_2(esk4_0,esk5_0,esk1_2(esk4_0,esk6_0))|~m1_subset_1(esk1_2(esk4_0,esk6_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7]), c_0_8])])).
% 0.22/0.39  cnf(c_0_12, plain, (r1_orders_2(X1,esk1_2(X1,X2),esk1_2(X1,X3))|~r2_lattice3(X1,X2,esk1_2(X1,X3))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.22/0.39  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_14, negated_conjecture, (k1_yellow_0(esk4_0,esk6_0)=esk5_0|r1_orders_2(esk4_0,esk5_0,esk1_2(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_10]), c_0_7]), c_0_8])]), ['final']).
% 0.22/0.39  cnf(c_0_15, plain, (r1_orders_2(X1,esk1_2(X1,X2),esk1_2(X1,X2))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_6]), ['final']).
% 0.22/0.39  cnf(c_0_16, negated_conjecture, (r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk5_0)|~r2_lattice3(esk4_0,X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_13]), c_0_7]), c_0_8])]), ['final']).
% 0.22/0.39  cnf(c_0_17, plain, (r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.22/0.39  cnf(c_0_18, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.22/0.39  cnf(c_0_19, plain, (v3_lattice3(X1)|~r1_orders_2(X1,X2,esk3_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.22/0.39  cnf(c_0_20, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk7_0)|~r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0!=k1_yellow_0(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))|~r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0!=k1_yellow_0(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_22, negated_conjecture, (r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0=k1_yellow_0(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_23, negated_conjecture, (~r1_orders_2(esk4_0,esk5_0,esk7_0)|~r2_lattice3(esk4_0,esk6_0,esk5_0)|esk5_0!=k1_yellow_0(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  cnf(c_0_25, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.22/0.39  # SZS output end Saturation
% 0.22/0.39  # Proof object total steps             : 26
% 0.22/0.39  # Proof object clause steps            : 21
% 0.22/0.39  # Proof object formula steps           : 5
% 0.22/0.39  # Proof object conjectures             : 16
% 0.22/0.39  # Proof object clause conjectures      : 13
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 16
% 0.22/0.39  # Proof object initial formulas used   : 2
% 0.22/0.39  # Proof object generating inferences   : 5
% 0.22/0.39  # Proof object simplifying inferences  : 9
% 0.22/0.39  # Parsed axioms                        : 2
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 16
% 0.22/0.39  # Removed in clause preprocessing      : 0
% 0.22/0.39  # Initial clauses in saturation        : 16
% 0.22/0.39  # Processed clauses                    : 21
% 0.22/0.39  # ...of these trivial                  : 0
% 0.22/0.39  # ...subsumed                          : 0
% 0.22/0.39  # ...remaining for further processing  : 21
% 0.22/0.39  # Other redundant clauses eliminated   : 0
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 1
% 0.22/0.39  # Backward-rewritten                   : 0
% 0.22/0.39  # Generated clauses                    : 14
% 0.22/0.39  # ...of the previous two non-trivial   : 5
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 14
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 0
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 20
% 0.22/0.39  #    Positive orientable unit clauses  : 4
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 1
% 0.22/0.39  #    Non-unit-clauses                  : 15
% 0.22/0.39  # Current number of unprocessed clauses: 0
% 0.22/0.39  # ...number of literals in the above   : 0
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 1
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 24
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 2
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.22/0.39  # Unit Clause-clause subsumption calls : 0
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 0
% 0.22/0.39  # BW rewrite match successes           : 0
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 1495
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.025 s
% 0.22/0.39  # System time              : 0.006 s
% 0.22/0.39  # Total time               : 0.031 s
% 0.22/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
