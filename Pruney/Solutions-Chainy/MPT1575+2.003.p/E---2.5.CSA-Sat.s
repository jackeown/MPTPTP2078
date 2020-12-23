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
% DateTime   : Thu Dec  3 11:15:35 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  67 expanded)
%              Number of clauses        :   19 (  25 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :  100 ( 337 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_yellow_0(X1,X2) )
       => v3_lattice3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_yellow_0(X1,X2) )
         => v3_lattice3(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t53_yellow_0])).

fof(c_0_6,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_7,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_8,negated_conjecture,(
    ! [X19] :
      ( ~ v2_struct_0(esk4_0)
      & l1_orders_2(esk4_0)
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | r1_yellow_0(esk4_0,X19) )
      & ~ v3_lattice3(esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( r1_yellow_0(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

fof(c_0_13,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_14,plain,(
    ! [X11,X12,X14,X16] :
      ( ( m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))
        | ~ v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_lattice3(X11,X12,esk1_2(X11,X12))
        | ~ v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_lattice3(X11,X12,X14)
        | r1_orders_2(X11,esk1_2(X11,X12),X14)
        | ~ v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk3_2(X11,X16),u1_struct_0(X11))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | ~ r2_lattice3(X11,esk2_1(X11),X16)
        | v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_lattice3(X11,esk2_1(X11),esk3_2(X11,X16))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | ~ r2_lattice3(X11,esk2_1(X11),X16)
        | v3_lattice3(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X16,esk3_2(X11,X16))
        | ~ m1_subset_1(X16,u1_struct_0(X11))
        | ~ r2_lattice3(X11,esk2_1(X11),X16)
        | v3_lattice3(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_yellow_0(esk4_0,k3_xboole_0(u1_struct_0(esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12]),
    [final]).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_17,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_18,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_19,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_21,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_22,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( ~ v3_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r1_yellow_0(esk4_0,k3_xboole_0(X1,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_27,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16]),
    [final]).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_16]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.20/0.39  # and selection function SelectDiffNegLit.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.041 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # No proof found!
% 0.20/0.39  # SZS status CounterSatisfiable
% 0.20/0.39  # SZS output start Saturation
% 0.20/0.39  fof(t53_yellow_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>(![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_yellow_0(X1,X2))=>v3_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_yellow_0)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.39  fof(d12_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v3_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_lattice3)).
% 0.20/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>(![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_yellow_0(X1,X2))=>v3_lattice3(X1)))), inference(assume_negation,[status(cth)],[t53_yellow_0])).
% 0.20/0.39  fof(c_0_6, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.39  fof(c_0_7, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.39  fof(c_0_8, negated_conjecture, ![X19]:((~v2_struct_0(esk4_0)&l1_orders_2(esk4_0))&((~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(esk4_0)))|r1_yellow_0(esk4_0,X19))&~v3_lattice3(esk4_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).
% 0.20/0.39  cnf(c_0_9, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.39  cnf(c_0_10, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.39  cnf(c_0_11, negated_conjecture, (r1_yellow_0(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.39  cnf(c_0_12, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.20/0.39  fof(c_0_13, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.39  fof(c_0_14, plain, ![X11, X12, X14, X16]:((((m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))|~v3_lattice3(X11)|~l1_orders_2(X11))&(r2_lattice3(X11,X12,esk1_2(X11,X12))|~v3_lattice3(X11)|~l1_orders_2(X11)))&(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_lattice3(X11,X12,X14)|r1_orders_2(X11,esk1_2(X11,X12),X14))|~v3_lattice3(X11)|~l1_orders_2(X11)))&((m1_subset_1(esk3_2(X11,X16),u1_struct_0(X11))|(~m1_subset_1(X16,u1_struct_0(X11))|~r2_lattice3(X11,esk2_1(X11),X16))|v3_lattice3(X11)|~l1_orders_2(X11))&((r2_lattice3(X11,esk2_1(X11),esk3_2(X11,X16))|(~m1_subset_1(X16,u1_struct_0(X11))|~r2_lattice3(X11,esk2_1(X11),X16))|v3_lattice3(X11)|~l1_orders_2(X11))&(~r1_orders_2(X11,X16,esk3_2(X11,X16))|(~m1_subset_1(X16,u1_struct_0(X11))|~r2_lattice3(X11,esk2_1(X11),X16))|v3_lattice3(X11)|~l1_orders_2(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (r1_yellow_0(esk4_0,k3_xboole_0(u1_struct_0(esk4_0),X1))), inference(spm,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.20/0.39  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.20/0.39  cnf(c_0_17, plain, (r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.39  cnf(c_0_18, plain, (r1_orders_2(X2,esk1_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~v3_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.39  cnf(c_0_19, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.39  cnf(c_0_20, plain, (v3_lattice3(X1)|~r1_orders_2(X1,X2,esk3_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.39  cnf(c_0_21, plain, (r2_lattice3(X1,X2,esk1_2(X1,X2))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.39  cnf(c_0_22, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (~v3_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (r1_yellow_0(esk4_0,k3_xboole_0(X1,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.20/0.39  cnf(c_0_27, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_12, c_0_16]), ['final']).
% 0.20/0.39  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_10, c_0_16]), ['final']).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.20/0.39  # SZS output end Saturation
% 0.20/0.39  # Proof object total steps             : 30
% 0.20/0.39  # Proof object clause steps            : 19
% 0.20/0.39  # Proof object formula steps           : 11
% 0.20/0.39  # Proof object conjectures             : 9
% 0.20/0.39  # Proof object clause conjectures      : 6
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 14
% 0.20/0.39  # Proof object initial formulas used   : 5
% 0.20/0.39  # Proof object generating inferences   : 5
% 0.20/0.39  # Proof object simplifying inferences  : 0
% 0.20/0.39  # Parsed axioms                        : 5
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 14
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 14
% 0.20/0.39  # Processed clauses                    : 38
% 0.20/0.39  # ...of these trivial                  : 5
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 33
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 18
% 0.20/0.39  # ...of the previous two non-trivial   : 10
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 18
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 19
% 0.20/0.39  #    Positive orientable unit clauses  : 7
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 9
% 0.20/0.39  # Current number of unprocessed clauses: 0
% 0.20/0.39  # ...number of literals in the above   : 0
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 14
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 50
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 2
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.39  # Unit Clause-clause subsumption calls : 2
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 4
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1237
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.043 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.047 s
% 0.20/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
