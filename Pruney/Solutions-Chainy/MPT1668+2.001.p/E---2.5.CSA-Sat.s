%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:24 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   40 (  87 expanded)
%              Number of clauses        :   27 (  29 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :  155 ( 660 expanded)
%              Number of equality atoms :   13 (  61 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v14_waybel_0(X2,X1)
          <=> ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & X2 = k5_waybel_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_waybel_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v14_waybel_0(X2,X1)
            <=> ? [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                  & X2 = k5_waybel_0(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_waybel_0])).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_9,negated_conjecture,(
    ! [X21] :
      ( ~ v2_struct_0(esk2_0)
      & v3_orders_2(esk2_0)
      & v4_orders_2(esk2_0)
      & l1_orders_2(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & v1_waybel_0(esk3_0,esk2_0)
      & v12_waybel_0(esk3_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( ~ v14_waybel_0(esk3_0,esk2_0)
        | ~ m1_subset_1(X21,u1_struct_0(esk2_0))
        | esk3_0 != k5_waybel_0(esk2_0,X21) )
      & ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
        | v14_waybel_0(esk3_0,esk2_0) )
      & ( esk3_0 = k5_waybel_0(esk2_0,esk4_0)
        | v14_waybel_0(esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_15,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X17,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,esk1_3(X14,X15,X16),X16)
        | r2_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_12]),
    [final]).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ v3_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | r1_orders_2(X12,X13,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12]),
    [final]).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r1_tarski(u1_struct_0(esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17]),
    [final]).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_26,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( ~ v14_waybel_0(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | esk3_0 != k5_waybel_0(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk3_0
    | ~ r1_tarski(u1_struct_0(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    | v14_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = k5_waybel_0(esk2_0,esk4_0)
    | v14_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( v1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:02:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.028 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # No proof found!
% 0.18/0.36  # SZS status CounterSatisfiable
% 0.18/0.36  # SZS output start Saturation
% 0.18/0.36  fof(t48_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&v12_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v14_waybel_0(X2,X1)<=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&X2=k5_waybel_0(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_waybel_0)).
% 0.18/0.36  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.18/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.36  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.18/0.36  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.18/0.36  fof(c_0_6, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&v12_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v14_waybel_0(X2,X1)<=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&X2=k5_waybel_0(X1,X3)))))), inference(assume_negation,[status(cth)],[t48_waybel_0])).
% 0.18/0.36  fof(c_0_7, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.18/0.36  fof(c_0_8, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.36  fof(c_0_9, negated_conjecture, ![X21]:((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&((((~v1_xboole_0(esk3_0)&v1_waybel_0(esk3_0,esk2_0))&v12_waybel_0(esk3_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))))&((~v14_waybel_0(esk3_0,esk2_0)|(~m1_subset_1(X21,u1_struct_0(esk2_0))|esk3_0!=k5_waybel_0(esk2_0,X21)))&((m1_subset_1(esk4_0,u1_struct_0(esk2_0))|v14_waybel_0(esk3_0,esk2_0))&(esk3_0=k5_waybel_0(esk2_0,esk4_0)|v14_waybel_0(esk3_0,esk2_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).
% 0.18/0.36  cnf(c_0_10, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.18/0.36  cnf(c_0_11, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  fof(c_0_13, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.36  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  fof(c_0_15, plain, ![X14, X15, X16, X17]:((~r2_lattice3(X14,X15,X16)|(~m1_subset_1(X17,u1_struct_0(X14))|(~r2_hidden(X17,X15)|r1_orders_2(X14,X17,X16)))|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((m1_subset_1(esk1_3(X14,X15,X16),u1_struct_0(X14))|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&((r2_hidden(esk1_3(X14,X15,X16),X15)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))&(~r1_orders_2(X14,esk1_3(X14,X15,X16),X16)|r2_lattice3(X14,X15,X16)|~m1_subset_1(X16,u1_struct_0(X14))|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.18/0.36  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_12]), ['final']).
% 0.18/0.36  fof(c_0_18, plain, ![X12, X13]:(v2_struct_0(X12)|~v3_orders_2(X12)|~l1_orders_2(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|r1_orders_2(X12,X13,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.18/0.36  cnf(c_0_19, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_14, c_0_12]), ['final']).
% 0.18/0.36  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_22, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk3_0)|~r1_tarski(u1_struct_0(esk2_0),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.18/0.36  cnf(c_0_24, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_25, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_26, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_27, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (~v14_waybel_0(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|esk3_0!=k5_waybel_0(esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk2_0)=esk3_0|~r1_tarski(u1_struct_0(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.18/0.36  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))|v14_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_31, negated_conjecture, (esk3_0=k5_waybel_0(esk2_0,esk4_0)|v14_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_34, negated_conjecture, (v12_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21]), ['final']).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (v1_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_37, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_38, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.36  # SZS output end Saturation
% 0.18/0.36  # Proof object total steps             : 40
% 0.18/0.36  # Proof object clause steps            : 27
% 0.18/0.36  # Proof object formula steps           : 13
% 0.18/0.36  # Proof object conjectures             : 18
% 0.18/0.36  # Proof object clause conjectures      : 15
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 21
% 0.18/0.36  # Proof object initial formulas used   : 6
% 0.18/0.36  # Proof object generating inferences   : 5
% 0.18/0.36  # Proof object simplifying inferences  : 1
% 0.18/0.36  # Parsed axioms                        : 6
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 22
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 22
% 0.18/0.36  # Processed clauses                    : 50
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 1
% 0.18/0.36  # ...remaining for further processing  : 49
% 0.18/0.36  # Other redundant clauses eliminated   : 2
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 0
% 0.18/0.36  # Generated clauses                    : 10
% 0.18/0.36  # ...of the previous two non-trivial   : 7
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 8
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 2
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 26
% 0.18/0.36  #    Positive orientable unit clauses  : 8
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 2
% 0.18/0.36  #    Non-unit-clauses                  : 16
% 0.18/0.36  # Current number of unprocessed clauses: 0
% 0.18/0.36  # ...number of literals in the above   : 0
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 21
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 27
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 13
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.18/0.36  # Unit Clause-clause subsumption calls : 1
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 0
% 0.18/0.36  # BW rewrite match successes           : 0
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 1680
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.031 s
% 0.18/0.36  # System time              : 0.002 s
% 0.18/0.36  # Total time               : 0.033 s
% 0.18/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
