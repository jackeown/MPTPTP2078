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
% DateTime   : Thu Dec  3 11:15:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 (2789 expanded)
%              Number of clauses        :   44 (1255 expanded)
%              Number of leaves         :    7 ( 646 expanded)
%              Depth                    :   16
%              Number of atoms          :  189 (10330 expanded)
%              Number of equality atoms :   20 (1459 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r2_lattice3(X1,k1_xboole_0,X2)
              & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_yellow_0])).

fof(c_0_8,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ r2_hidden(X14,X13)
      | r2_hidden(X14,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_9,plain,(
    ! [X15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_10,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X23)
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X24,esk2_3(X22,X23,X24))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_11,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ r2_lattice3(esk4_0,k1_xboole_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k1_xboole_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X30,X28)
        | r1_orders_2(X27,X30,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk3_3(X27,X28,X29),u1_struct_0(X27))
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( r2_hidden(esk3_3(X27,X28,X29),X28)
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,esk3_3(X27,X28,X29),X29)
        | r2_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_19,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(esk4_0,k1_xboole_0,esk5_0)
    | r2_hidden(esk2_3(esk4_0,k1_xboole_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk3_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17])])).

cnf(c_0_26,negated_conjecture,
    ( esk2_3(esk4_0,k1_xboole_0,esk5_0) = X1
    | r1_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk4_0,k1_xboole_0,esk5_0)
    | r2_hidden(esk3_3(esk4_0,k1_xboole_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( X1 = X2
    | r1_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( esk3_3(esk4_0,k1_xboole_0,esk5_0) = X1
    | r2_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | m1_subset_1(esk3_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17])])).

cnf(c_0_32,negated_conjecture,
    ( r1_lattice3(esk4_0,k1_xboole_0,esk5_0)
    | m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k1_xboole_0,esk5_0)
    | ~ r1_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( X1 = X2
    | r2_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk4_0,k1_xboole_0,esk5_0)
    | m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_lattice3(esk4_0,k1_xboole_0,esk5_0)
    | m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( X1 = X2 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35]),c_0_36])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

fof(c_0_43,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_orders_2(X19,X20,X21)
        | r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))
        | r1_orders_2(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k1_xboole_0,X1)
    | ~ r1_lattice3(esk4_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_46,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk3_3(X1,X2,X3),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),c_0_42])])).

cnf(c_0_47,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_49,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,X1,X2)
    | ~ r1_lattice3(esk4_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_37])).

cnf(c_0_52,plain,
    ( r1_orders_2(X1,X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_41])]),c_0_42]),c_0_42]),c_0_48])])).

cnf(c_0_53,plain,
    ( r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,esk2_3(X1,X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_41])]),c_0_42])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_lattice3(X1,X2,X3)
    | ~ r1_lattice3(X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(X1,X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( r1_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(spm,[status(thm)],[c_0_53,c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_lattice3(X1,X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_52])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t6_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.13/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.13/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.39  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.13/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.39  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.39  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.13/0.39  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2))))), inference(assume_negation,[status(cth)],[t6_yellow_0])).
% 0.13/0.39  fof(c_0_8, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|(~r2_hidden(X14,X13)|r2_hidden(X14,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.13/0.39  fof(c_0_9, plain, ![X15]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.39  fof(c_0_10, plain, ![X22, X23, X24, X25]:((~r1_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X23)|r1_orders_2(X22,X24,X25)))|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_hidden(esk2_3(X22,X23,X24),X23)|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,X24,esk2_3(X22,X23,X24))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.13/0.39  fof(c_0_11, negated_conjecture, (l1_orders_2(esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(~r2_lattice3(esk4_0,k1_xboole_0,esk5_0)|~r1_lattice3(esk4_0,k1_xboole_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.39  fof(c_0_12, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.39  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_14, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  fof(c_0_18, plain, ![X27, X28, X29, X30]:((~r2_lattice3(X27,X28,X29)|(~m1_subset_1(X30,u1_struct_0(X27))|(~r2_hidden(X30,X28)|r1_orders_2(X27,X30,X29)))|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))&((m1_subset_1(esk3_3(X27,X28,X29),u1_struct_0(X27))|r2_lattice3(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))&((r2_hidden(esk3_3(X27,X28,X29),X28)|r2_lattice3(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))&(~r1_orders_2(X27,esk3_3(X27,X28,X29),X29)|r2_lattice3(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~l1_orders_2(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.39  cnf(c_0_19, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (r1_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk2_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.13/0.39  cnf(c_0_22, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_23, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (r1_lattice3(esk4_0,k1_xboole_0,esk5_0)|r2_hidden(esk2_3(esk4_0,k1_xboole_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk3_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17])])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (esk2_3(esk4_0,k1_xboole_0,esk5_0)=X1|r1_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (r2_lattice3(esk4_0,k1_xboole_0,esk5_0)|r2_hidden(esk3_3(esk4_0,k1_xboole_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.13/0.39  cnf(c_0_28, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (X1=X2|r1_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (esk3_3(esk4_0,k1_xboole_0,esk5_0)=X1|r2_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|m1_subset_1(esk3_3(esk4_0,X1,esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_17])])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (r1_lattice3(esk4_0,k1_xboole_0,esk5_0)|m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_29])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (~r2_lattice3(esk4_0,k1_xboole_0,esk5_0)|~r1_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (X1=X2|r2_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_30])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r2_lattice3(esk4_0,k1_xboole_0,esk5_0)|m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r1_lattice3(esk4_0,k1_xboole_0,esk5_0)|m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (X1=X2), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35]), c_0_36])).
% 0.13/0.39  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_40, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_17, c_0_37])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.13/0.39  fof(c_0_43, plain, ![X19, X20, X21]:((~r1_orders_2(X19,X20,X21)|r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|~l1_orders_2(X19))&(~r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))|r1_orders_2(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|~l1_orders_2(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.13/0.39  cnf(c_0_44, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (~r2_lattice3(esk4_0,k1_xboole_0,X1)|~r1_lattice3(esk4_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 0.13/0.39  cnf(c_0_46, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk3_3(X1,X2,X3),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])]), c_0_42])])).
% 0.13/0.39  cnf(c_0_47, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_37])).
% 0.13/0.39  cnf(c_0_49, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (~r2_lattice3(esk4_0,X1,X2)|~r1_lattice3(esk4_0,X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_37])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,X4,X3)), inference(spm,[status(thm)],[c_0_46, c_0_37])).
% 0.13/0.39  cnf(c_0_52, plain, (r1_orders_2(X1,X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_41])]), c_0_42]), c_0_42]), c_0_48])])).
% 0.13/0.39  cnf(c_0_53, plain, (r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X3,esk2_3(X1,X2,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_41])]), c_0_42])])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (~r2_lattice3(X1,X2,X3)|~r1_lattice3(X1,X2,X3)), inference(spm,[status(thm)],[c_0_50, c_0_37])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (r2_lattice3(X1,X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (r1_lattice3(X1,X2,X3)|~r1_orders_2(X1,X3,X4)), inference(spm,[status(thm)],[c_0_53, c_0_37])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (~r1_lattice3(X1,X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_52])]), c_0_57]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 59
% 0.13/0.39  # Proof object clause steps            : 44
% 0.13/0.39  # Proof object formula steps           : 15
% 0.13/0.39  # Proof object conjectures             : 31
% 0.13/0.39  # Proof object clause conjectures      : 28
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 13
% 0.13/0.39  # Proof object initial formulas used   : 7
% 0.13/0.39  # Proof object generating inferences   : 23
% 0.13/0.39  # Proof object simplifying inferences  : 32
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 8
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 20
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 20
% 0.13/0.39  # Processed clauses                    : 177
% 0.13/0.39  # ...of these trivial                  : 7
% 0.13/0.39  # ...subsumed                          : 62
% 0.13/0.39  # ...remaining for further processing  : 107
% 0.13/0.39  # Other redundant clauses eliminated   : 12
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 44
% 0.13/0.39  # Backward-rewritten                   : 34
% 0.13/0.39  # Generated clauses                    : 816
% 0.13/0.39  # ...of the previous two non-trivial   : 784
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 803
% 0.13/0.39  # Factorizations                       : 2
% 0.13/0.39  # Equation resolutions                 : 12
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 7
% 0.13/0.39  #    Positive orientable unit clauses  : 5
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 0
% 0.13/0.39  # Current number of unprocessed clauses: 191
% 0.13/0.39  # ...number of literals in the above   : 902
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 98
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 924
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 433
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 94
% 0.13/0.39  # Unit Clause-clause subsumption calls : 102
% 0.13/0.39  # Rewrite failures with RHS unbound    : 98
% 0.13/0.39  # BW rewrite match attempts            : 79
% 0.13/0.39  # BW rewrite match successes           : 75
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 10338
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.042 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
