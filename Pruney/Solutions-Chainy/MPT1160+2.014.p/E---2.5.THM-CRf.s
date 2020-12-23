%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:55 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 120 expanded)
%              Number of clauses        :   29 (  45 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 537 expanded)
%              Number of equality atoms :   17 (  76 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_orders_2(X1,k1_struct_0(X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k1_struct_0(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k3_orders_2(X1,k1_struct_0(X1),X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t60_orders_2])).

fof(c_0_11,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ v4_orders_2(X17)
      | ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | m1_subset_1(k3_orders_2(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_21,plain,(
    ! [X16] :
      ( ~ l1_struct_0(X16)
      | k1_struct_0(X16) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).

fof(c_0_22,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_23,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X21,X22,X23,X24] :
      ( ( r2_orders_2(X21,X22,X23)
        | ~ r2_hidden(X22,k3_orders_2(X21,X24,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( r2_hidden(X22,X24)
        | ~ r2_hidden(X22,k3_orders_2(X21,X24,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) )
      & ( ~ r2_orders_2(X21,X22,X23)
        | ~ r2_hidden(X22,X24)
        | r2_hidden(X22,k3_orders_2(X21,X24,X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,plain,(
    ! [X12,X14,X15] :
      ( ( r2_hidden(esk1_1(X12),X12)
        | X12 = k1_xboole_0 )
      & ( ~ r2_hidden(X14,X12)
        | esk1_1(X12) != k4_tarski(X14,X15)
        | X12 = k1_xboole_0 )
      & ( ~ r2_hidden(X15,X12)
        | esk1_1(X12) != k4_tarski(X14,X15)
        | X12 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_32,negated_conjecture,
    ( k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k3_orders_2(esk2_0,k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

fof(c_0_40,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ v1_xboole_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),X1)
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0)
    | ~ r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_46,c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.39  # and selection function SelectNewComplexAHPNS.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t60_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_orders_2(X1,k1_struct_0(X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 0.19/0.39  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.19/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.39  fof(d2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k1_struct_0(X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 0.19/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.39  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.19/0.39  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.19/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_orders_2(X1,k1_struct_0(X1),X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t60_orders_2])).
% 0.19/0.39  fof(c_0_11, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~m1_subset_1(X19,u1_struct_0(X17))|m1_subset_1(k3_orders_2(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.19/0.39  fof(c_0_12, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.39  cnf(c_0_13, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  fof(c_0_20, plain, ![X5]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.39  fof(c_0_21, plain, ![X16]:(~l1_struct_0(X16)|k1_struct_0(X16)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).
% 0.19/0.39  fof(c_0_22, plain, ![X20]:(~l1_orders_2(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.39  fof(c_0_23, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.39  cnf(c_0_25, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_26, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_27, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  fof(c_0_28, plain, ![X21, X22, X23, X24]:(((r2_orders_2(X21,X22,X23)|~r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)))&(r2_hidden(X22,X24)|~r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21))))&(~r2_orders_2(X21,X22,X23)|~r2_hidden(X22,X24)|r2_hidden(X22,k3_orders_2(X21,X24,X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.19/0.39  cnf(c_0_29, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.39  fof(c_0_31, plain, ![X12, X14, X15]:((r2_hidden(esk1_1(X12),X12)|X12=k1_xboole_0)&((~r2_hidden(X14,X12)|esk1_1(X12)!=k4_tarski(X14,X15)|X12=k1_xboole_0)&(~r2_hidden(X15,X12)|esk1_1(X12)!=k4_tarski(X14,X15)|X12=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_33, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.39  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.39  cnf(c_0_36, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (k3_orders_2(esk2_0,k1_xboole_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_15])])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.19/0.39  fof(c_0_40, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|~v1_xboole_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),X1)|~r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.39  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0)|~r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.19/0.39  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_36]), c_0_37])).
% 0.19/0.39  cnf(c_0_46, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.39  cnf(c_0_48, plain, ($false), inference(sr,[status(thm)],[c_0_46, c_0_47]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 49
% 0.19/0.39  # Proof object clause steps            : 29
% 0.19/0.39  # Proof object formula steps           : 20
% 0.19/0.39  # Proof object conjectures             : 20
% 0.19/0.39  # Proof object clause conjectures      : 17
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 12
% 0.19/0.39  # Proof object simplifying inferences  : 17
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 10
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 20
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 20
% 0.19/0.39  # Processed clauses                    : 124
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 0
% 0.19/0.39  # ...remaining for further processing  : 124
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 230
% 0.19/0.39  # ...of the previous two non-trivial   : 229
% 0.19/0.39  # Contextual simplify-reflections      : 1
% 0.19/0.39  # Paramodulations                      : 229
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 122
% 0.19/0.39  #    Positive orientable unit clauses  : 27
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 4
% 0.19/0.39  #    Non-unit-clauses                  : 91
% 0.19/0.39  # Current number of unprocessed clauses: 125
% 0.19/0.39  # ...number of literals in the above   : 325
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 2
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1151
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 986
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.39  # Unit Clause-clause subsumption calls : 128
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 138
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 124
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 10392
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.036 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.042 s
% 0.19/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
