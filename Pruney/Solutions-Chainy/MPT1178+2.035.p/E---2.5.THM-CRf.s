%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:16 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 233 expanded)
%              Number of clauses        :   27 (  77 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  192 (1282 expanded)
%              Number of equality atoms :   25 ( 174 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(t82_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ~ r1_xboole_0(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(existence_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ? [X3] : m2_orders_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t98_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X15,X14)
        | m2_orders_2(X15,X12,X13)
        | X14 != k4_orders_2(X12,X13)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ m2_orders_2(X16,X12,X13)
        | r2_hidden(X16,X14)
        | X14 != k4_orders_2(X12,X13)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ r2_hidden(esk3_3(X12,X13,X17),X17)
        | ~ m2_orders_2(esk3_3(X12,X13,X17),X12,X13)
        | X17 = k4_orders_2(X12,X13)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk3_3(X12,X13,X17),X17)
        | m2_orders_2(esk3_3(X12,X13,X17),X12,X13)
        | X17 = k4_orders_2(X12,X13)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26,X27] :
      ( v2_struct_0(X24)
      | ~ v3_orders_2(X24)
      | ~ v4_orders_2(X24)
      | ~ v5_orders_2(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_orders_1(X25,k1_orders_1(u1_struct_0(X24)))
      | ~ m2_orders_2(X26,X24,X25)
      | ~ m2_orders_2(X27,X24,X25)
      | ~ r1_xboole_0(X26,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0)))
    & k3_tarski(k4_orders_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v3_orders_2(X19)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(X19)))
      | m2_orders_2(esk4_2(X19,X20),X19,X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk4_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X28,X29,X30] :
      ( ( X29 = k1_xboole_0
        | ~ r2_hidden(X29,X28)
        | k3_tarski(X28) != k1_xboole_0 )
      & ( esk5_1(X30) != k1_xboole_0
        | k3_tarski(X30) = k1_xboole_0 )
      & ( r2_hidden(esk5_1(X30),X30)
        | k3_tarski(X30) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k4_orders_2(X1,X3))
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_26,plain,(
    ! [X9,X10] :
      ( ( r2_hidden(esk2_2(X9,X10),X9)
        | r1_xboole_0(k3_tarski(X9),X10) )
      & ( ~ r1_xboole_0(esk2_2(X9,X10),X10)
        | r1_xboole_0(k3_tarski(X9),X10) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).

cnf(c_0_27,negated_conjecture,
    ( ~ m2_orders_2(X1,esk6_0,esk7_0)
    | ~ m2_orders_2(X2,esk6_0,esk7_0)
    | ~ r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m2_orders_2(esk4_2(esk6_0,esk7_0),esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k4_orders_2(esk6_0,esk7_0))
    | ~ m2_orders_2(X1,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ m2_orders_2(X1,esk6_0,esk7_0)
    | ~ r1_xboole_0(X1,esk4_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k4_orders_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk7_0),k4_orders_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k3_tarski(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_xboole_0(esk4_2(esk6_0,esk7_0),esk4_2(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( esk4_2(esk6_0,esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:47:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.20/0.36  # and selection function SelectNewComplexAHPNS.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.016 s
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 0.20/0.36  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 0.20/0.36  fof(t82_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>~(r1_xboole_0(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 0.20/0.36  fof(existence_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>?[X3]:m2_orders_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 0.20/0.36  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.20/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.36  fof(t98_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_xboole_0(X3,X2))=>r1_xboole_0(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 0.20/0.36  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.20/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.36  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.20/0.36  fof(c_0_10, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X15,X14)|m2_orders_2(X15,X12,X13)|X14!=k4_orders_2(X12,X13)|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))&(~m2_orders_2(X16,X12,X13)|r2_hidden(X16,X14)|X14!=k4_orders_2(X12,X13)|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12))))&((~r2_hidden(esk3_3(X12,X13,X17),X17)|~m2_orders_2(esk3_3(X12,X13,X17),X12,X13)|X17=k4_orders_2(X12,X13)|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))&(r2_hidden(esk3_3(X12,X13,X17),X17)|m2_orders_2(esk3_3(X12,X13,X17),X12,X13)|X17=k4_orders_2(X12,X13)|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.20/0.36  fof(c_0_11, plain, ![X24, X25, X26, X27]:(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|(~m1_orders_1(X25,k1_orders_1(u1_struct_0(X24)))|(~m2_orders_2(X26,X24,X25)|(~m2_orders_2(X27,X24,X25)|~r1_xboole_0(X26,X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).
% 0.20/0.36  fof(c_0_12, negated_conjecture, (((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&v5_orders_2(esk6_0))&l1_orders_2(esk6_0))&(m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0)))&k3_tarski(k4_orders_2(esk6_0,esk7_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.36  fof(c_0_13, plain, ![X19, X20]:(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_orders_1(X20,k1_orders_1(u1_struct_0(X19)))|m2_orders_2(esk4_2(X19,X20),X19,X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).
% 0.20/0.36  cnf(c_0_14, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.36  cnf(c_0_15, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)|~m2_orders_2(X4,X1,X2)|~r1_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.36  cnf(c_0_16, negated_conjecture, (m1_orders_1(esk7_0,k1_orders_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_18, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_19, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_20, negated_conjecture, (v3_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_22, plain, (v2_struct_0(X1)|m2_orders_2(esk4_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.36  fof(c_0_23, plain, ![X28, X29, X30]:((X29=k1_xboole_0|~r2_hidden(X29,X28)|k3_tarski(X28)!=k1_xboole_0)&((esk5_1(X30)!=k1_xboole_0|k3_tarski(X30)=k1_xboole_0)&(r2_hidden(esk5_1(X30),X30)|k3_tarski(X30)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.20/0.36  cnf(c_0_24, plain, (v2_struct_0(X1)|r2_hidden(X2,k4_orders_2(X1,X3))|~m2_orders_2(X2,X1,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.36  fof(c_0_25, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.36  fof(c_0_26, plain, ![X9, X10]:((r2_hidden(esk2_2(X9,X10),X9)|r1_xboole_0(k3_tarski(X9),X10))&(~r1_xboole_0(esk2_2(X9,X10),X10)|r1_xboole_0(k3_tarski(X9),X10))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).
% 0.20/0.36  cnf(c_0_27, negated_conjecture, (~m2_orders_2(X1,esk6_0,esk7_0)|~m2_orders_2(X2,esk6_0,esk7_0)|~r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.36  cnf(c_0_28, negated_conjecture, (m2_orders_2(esk4_2(esk6_0,esk7_0),esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.36  cnf(c_0_29, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.36  cnf(c_0_30, negated_conjecture, (k3_tarski(k4_orders_2(esk6_0,esk7_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k4_orders_2(esk6_0,esk7_0))|~m2_orders_2(X1,esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.36  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.36  cnf(c_0_33, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.36  cnf(c_0_34, negated_conjecture, (~m2_orders_2(X1,esk6_0,esk7_0)|~r1_xboole_0(X1,esk4_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.36  cnf(c_0_35, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(X1,k4_orders_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.36  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk7_0),k4_orders_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 0.20/0.36  cnf(c_0_37, plain, (r1_xboole_0(k3_tarski(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.36  cnf(c_0_38, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.20/0.36  cnf(c_0_39, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.36  cnf(c_0_40, negated_conjecture, (~r1_xboole_0(esk4_2(esk6_0,esk7_0),esk4_2(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.20/0.36  cnf(c_0_41, negated_conjecture, (esk4_2(esk6_0,esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.36  cnf(c_0_42, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.20/0.36  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_41]), c_0_42])]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 44
% 0.20/0.36  # Proof object clause steps            : 27
% 0.20/0.36  # Proof object formula steps           : 17
% 0.20/0.36  # Proof object conjectures             : 19
% 0.20/0.36  # Proof object clause conjectures      : 16
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 15
% 0.20/0.36  # Proof object initial formulas used   : 9
% 0.20/0.36  # Proof object generating inferences   : 10
% 0.20/0.36  # Proof object simplifying inferences  : 25
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 10
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 23
% 0.20/0.36  # Removed in clause preprocessing      : 0
% 0.20/0.36  # Initial clauses in saturation        : 23
% 0.20/0.36  # Processed clauses                    : 48
% 0.20/0.36  # ...of these trivial                  : 3
% 0.20/0.36  # ...subsumed                          : 1
% 0.20/0.36  # ...remaining for further processing  : 44
% 0.20/0.36  # Other redundant clauses eliminated   : 2
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 0
% 0.20/0.36  # Backward-rewritten                   : 5
% 0.20/0.36  # Generated clauses                    : 40
% 0.20/0.36  # ...of the previous two non-trivial   : 33
% 0.20/0.36  # Contextual simplify-reflections      : 0
% 0.20/0.36  # Paramodulations                      : 37
% 0.20/0.36  # Factorizations                       : 0
% 0.20/0.36  # Equation resolutions                 : 2
% 0.20/0.36  # Propositional unsat checks           : 0
% 0.20/0.36  #    Propositional check models        : 0
% 0.20/0.36  #    Propositional check unsatisfiable : 0
% 0.20/0.36  #    Propositional clauses             : 0
% 0.20/0.36  #    Propositional clauses after purity: 0
% 0.20/0.36  #    Propositional unsat core size     : 0
% 0.20/0.36  #    Propositional preprocessing time  : 0.000
% 0.20/0.36  #    Propositional encoding time       : 0.000
% 0.20/0.36  #    Propositional solver time         : 0.000
% 0.20/0.36  #    Success case prop preproc time    : 0.000
% 0.20/0.36  #    Success case prop encoding time   : 0.000
% 0.20/0.36  #    Success case prop solver time     : 0.000
% 0.20/0.36  # Current number of processed clauses  : 36
% 0.20/0.36  #    Positive orientable unit clauses  : 12
% 0.20/0.36  #    Positive unorientable unit clauses: 0
% 0.20/0.36  #    Negative unit clauses             : 2
% 0.20/0.36  #    Non-unit-clauses                  : 22
% 0.20/0.36  # Current number of unprocessed clauses: 7
% 0.20/0.36  # ...number of literals in the above   : 28
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 6
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 98
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 33
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.36  # Unit Clause-clause subsumption calls : 19
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 2
% 0.20/0.36  # BW rewrite match successes           : 2
% 0.20/0.36  # Condensation attempts                : 48
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 2784
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.021 s
% 0.20/0.36  # System time              : 0.000 s
% 0.20/0.36  # Total time               : 0.021 s
% 0.20/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
