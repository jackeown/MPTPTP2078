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
% DateTime   : Thu Dec  3 11:16:18 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   25 (  63 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    3 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :  126 ( 428 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(t33_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_yellow_0(X1,X2)
           => k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_0)).

fof(c_0_3,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_lattice3(X5,X6,X7)
        | X7 != k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r2_lattice3(X5,X6,X8)
        | r1_orders_2(X5,X7,X8)
        | X7 != k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))
        | ~ r2_lattice3(X5,X6,X7)
        | X7 = k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( r2_lattice3(X5,X6,esk1_3(X5,X6,X7))
        | ~ r2_lattice3(X5,X6,X7)
        | X7 = k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X7,esk1_3(X5,X6,X7))
        | ~ r2_lattice3(X5,X6,X7)
        | X7 = k1_yellow_0(X5,X6)
        | ~ r1_yellow_0(X5,X6)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_4,plain,(
    ! [X10,X11] :
      ( ~ l1_orders_2(X10)
      | m1_subset_1(k1_yellow_0(X10,X11),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_5,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r1_yellow_0(X1,X2)
             => k1_yellow_0(X1,X2) = k1_yellow_0(X1,k3_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_waybel_0])).

cnf(c_0_9,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_10,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_5]),c_0_6]),
    [final]).

cnf(c_0_11,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | m1_subset_1(esk1_3(X1,X3,k1_yellow_0(X1,X2)),u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_6]),
    [final]).

cnf(c_0_12,plain,
    ( r2_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_13,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r1_yellow_0(esk2_0,esk3_0)
    & k1_yellow_0(esk2_0,esk3_0) != k1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_15,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | ~ r2_lattice3(X1,X2,esk1_3(X1,X3,k1_yellow_0(X1,X2)))
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_6]),c_0_11]),
    [final]).

cnf(c_0_16,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X1,X3)
    | r2_lattice3(X1,X3,esk1_3(X1,X3,k1_yellow_0(X1,X2)))
    | ~ r2_lattice3(X1,X3,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_6]),
    [final]).

cnf(c_0_17,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_6]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( k1_yellow_0(esk2_0,esk3_0) != k1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # No proof found!
% 0.14/0.37  # SZS status CounterSatisfiable
% 0.14/0.37  # SZS output start Saturation
% 0.14/0.37  fof(d9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_yellow_0(X1,X2)=>(X3=k1_yellow_0(X1,X2)<=>(r2_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 0.14/0.37  fof(dt_k1_yellow_0, axiom, ![X1, X2]:(l1_orders_2(X1)=>m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 0.14/0.37  fof(t33_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_yellow_0(X1,X2)=>k1_yellow_0(X1,X2)=k1_yellow_0(X1,k3_waybel_0(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_0)).
% 0.14/0.37  fof(c_0_3, plain, ![X5, X6, X7, X8]:(((r2_lattice3(X5,X6,X7)|X7!=k1_yellow_0(X5,X6)|~r1_yellow_0(X5,X6)|~m1_subset_1(X7,u1_struct_0(X5))|~l1_orders_2(X5))&(~m1_subset_1(X8,u1_struct_0(X5))|(~r2_lattice3(X5,X6,X8)|r1_orders_2(X5,X7,X8))|X7!=k1_yellow_0(X5,X6)|~r1_yellow_0(X5,X6)|~m1_subset_1(X7,u1_struct_0(X5))|~l1_orders_2(X5)))&((m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X5))|~r2_lattice3(X5,X6,X7)|X7=k1_yellow_0(X5,X6)|~r1_yellow_0(X5,X6)|~m1_subset_1(X7,u1_struct_0(X5))|~l1_orders_2(X5))&((r2_lattice3(X5,X6,esk1_3(X5,X6,X7))|~r2_lattice3(X5,X6,X7)|X7=k1_yellow_0(X5,X6)|~r1_yellow_0(X5,X6)|~m1_subset_1(X7,u1_struct_0(X5))|~l1_orders_2(X5))&(~r1_orders_2(X5,X7,esk1_3(X5,X6,X7))|~r2_lattice3(X5,X6,X7)|X7=k1_yellow_0(X5,X6)|~r1_yellow_0(X5,X6)|~m1_subset_1(X7,u1_struct_0(X5))|~l1_orders_2(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).
% 0.14/0.37  fof(c_0_4, plain, ![X10, X11]:(~l1_orders_2(X10)|m1_subset_1(k1_yellow_0(X10,X11),u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).
% 0.14/0.37  cnf(c_0_5, plain, (r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|X4!=k1_yellow_0(X2,X3)|~r1_yellow_0(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.14/0.37  cnf(c_0_6, plain, (m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.14/0.37  cnf(c_0_7, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_yellow_0(X1,X2)=>k1_yellow_0(X1,X2)=k1_yellow_0(X1,k3_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t33_waybel_0])).
% 0.14/0.37  cnf(c_0_9, plain, (X2=k1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~r2_lattice3(X1,X3,X2)|~r1_yellow_0(X1,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.37  cnf(c_0_10, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),X3)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_5]), c_0_6]), ['final']).
% 0.14/0.37  cnf(c_0_11, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|m1_subset_1(esk1_3(X1,X3,k1_yellow_0(X1,X2)),u1_struct_0(X1))|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_7, c_0_6]), ['final']).
% 0.14/0.37  cnf(c_0_12, plain, (r2_lattice3(X1,X2,esk1_3(X1,X2,X3))|X3=k1_yellow_0(X1,X2)|~r2_lattice3(X1,X2,X3)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.14/0.37  cnf(c_0_13, plain, (r2_lattice3(X1,X2,X3)|X3!=k1_yellow_0(X1,X2)|~r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.14/0.37  fof(c_0_14, negated_conjecture, ((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_yellow_0(esk2_0,esk3_0)&k1_yellow_0(esk2_0,esk3_0)!=k1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.14/0.37  cnf(c_0_15, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|~r2_lattice3(X1,X2,esk1_3(X1,X3,k1_yellow_0(X1,X2)))|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X3)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_6]), c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_16, plain, (k1_yellow_0(X1,X2)=k1_yellow_0(X1,X3)|r2_lattice3(X1,X3,esk1_3(X1,X3,k1_yellow_0(X1,X2)))|~r2_lattice3(X1,X3,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_12, c_0_6]), ['final']).
% 0.14/0.37  cnf(c_0_17, plain, (r2_lattice3(X1,X2,k1_yellow_0(X1,X2))|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_6]), ['final']).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (k1_yellow_0(esk2_0,esk3_0)!=k1_yellow_0(esk2_0,k3_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (r1_yellow_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.37  # SZS output end Saturation
% 0.14/0.37  # Proof object total steps             : 25
% 0.14/0.37  # Proof object clause steps            : 18
% 0.14/0.37  # Proof object formula steps           : 7
% 0.14/0.37  # Proof object conjectures             : 10
% 0.14/0.37  # Proof object clause conjectures      : 7
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 13
% 0.14/0.37  # Proof object initial formulas used   : 3
% 0.14/0.37  # Proof object generating inferences   : 3
% 0.14/0.37  # Proof object simplifying inferences  : 6
% 0.14/0.37  # Parsed axioms                        : 3
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 13
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 13
% 0.14/0.37  # Processed clauses                    : 31
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 31
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 5
% 0.14/0.37  # ...of the previous two non-trivial   : 5
% 0.14/0.37  # Contextual simplify-reflections      : 4
% 0.14/0.37  # Paramodulations                      : 3
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 16
% 0.14/0.37  #    Positive orientable unit clauses  : 5
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 9
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 13
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 56
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.14/0.37  # Unit Clause-clause subsumption calls : 0
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1189
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.024 s
% 0.14/0.37  # System time              : 0.007 s
% 0.14/0.37  # Total time               : 0.031 s
% 0.14/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
