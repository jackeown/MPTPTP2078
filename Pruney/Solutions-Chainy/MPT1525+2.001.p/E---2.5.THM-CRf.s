%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:10 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   69 (5592 expanded)
%              Number of clauses        :   56 (2292 expanded)
%              Number of leaves         :    6 (1307 expanded)
%              Depth                    :   24
%              Number of atoms          :  259 (21335 expanded)
%              Number of equality atoms :   24 (5713 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t3_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & v3_lattice3(X1) )
           => v3_lattice3(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( X10 = X12
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_7,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & v3_lattice3(X1) )
             => v3_lattice3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow_0])).

cnf(c_0_9,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( l1_orders_2(esk5_0)
    & l1_orders_2(esk6_0)
    & g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))
    & v3_lattice3(esk5_0)
    & ~ v3_lattice3(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( u1_orders_2(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_16,negated_conjecture,
    ( u1_orders_2(esk5_0) = u1_orders_2(esk6_0) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_16]),c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk6_0)) = g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_16])).

fof(c_0_20,plain,(
    ! [X13,X14,X16,X18] :
      ( ( m1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))
        | ~ v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X14,esk1_2(X13,X14))
        | ~ v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X14,X16)
        | r1_orders_2(X13,esk1_2(X13,X14),X16)
        | ~ v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk3_2(X13,X18),u1_struct_0(X13))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | ~ r2_lattice3(X13,esk2_1(X13),X18)
        | v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,esk2_1(X13),esk3_2(X13,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | ~ r2_lattice3(X13,esk2_1(X13),X18)
        | v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_orders_2(X13,X18,esk3_2(X13,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | ~ r2_lattice3(X13,esk2_1(X13),X18)
        | v3_lattice3(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

fof(c_0_22,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r2_lattice3(X20,X21,X22)
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_hidden(X23,X21)
        | r1_orders_2(X20,X23,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( m1_subset_1(esk4_3(X20,X21,X22),u1_struct_0(X20))
        | r2_lattice3(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( r2_hidden(esk4_3(X20,X21,X22),X21)
        | r2_lattice3(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) )
      & ( ~ r1_orders_2(X20,esk4_3(X20,X21,X22),X22)
        | r2_lattice3(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk6_0) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v3_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,X1),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_14])])).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,X2)
    | ~ r2_lattice3(esk5_0,X3,X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_14])])).

cnf(c_0_31,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))
    | m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r1_orders_2(X5,X6,X7)
        | r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))
        | r1_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_34,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))
    | r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X3)
    | ~ r2_lattice3(esk5_0,X4,X3)
    | ~ r2_hidden(esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X4)
    | ~ m1_subset_1(X3,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))
    | r2_hidden(esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_29])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))
    | r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X3)
    | ~ r2_lattice3(esk5_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk6_0))
    | ~ r1_orders_2(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_14])]),c_0_24]),c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))
    | r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),esk1_2(esk5_0,X3))
    | ~ r2_lattice3(esk5_0,X1,esk1_2(esk5_0,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_41,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,X2)
    | ~ r1_orders_2(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_29])])).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))
    | r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),esk1_2(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25]),c_0_14])])).

cnf(c_0_44,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk4_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))
    | r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),esk1_2(esk5_0,X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28])]),c_0_31])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_28]),c_0_29])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v3_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,X2)
    | m1_subset_1(esk4_3(esk5_0,X1,X2),u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_14])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_28]),c_0_29])]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))
    | m1_subset_1(esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,X2)
    | r2_hidden(esk4_3(esk5_0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_14])])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))
    | r1_orders_2(esk6_0,esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X2)
    | ~ r2_lattice3(esk6_0,X3,X2)
    | ~ r2_hidden(esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_51]),c_0_29])])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))
    | r2_hidden(esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_14])]),c_0_24]),c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))
    | r1_orders_2(esk6_0,esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X2)
    | ~ r2_lattice3(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_58,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,X2)
    | ~ r1_orders_2(esk6_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_36]),c_0_29])])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))
    | r1_orders_2(esk6_0,esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))
    | ~ r2_lattice3(esk6_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( r2_lattice3(esk6_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_47]),c_0_28]),c_0_29])]),c_0_48])).

cnf(c_0_62,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk6_0,esk1_2(esk5_0,X1),X2)
    | ~ r2_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_58]),c_0_28]),c_0_25]),c_0_24]),c_0_14])])).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,X2)
    | ~ r1_orders_2(esk6_0,esk4_3(esk5_0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_59]),c_0_24]),c_0_14])]),c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( r2_lattice3(esk5_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))
    | r1_orders_2(esk6_0,esk4_3(esk5_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,X1)))
    | ~ r2_lattice3(esk6_0,esk2_1(esk6_0),esk1_2(esk5_0,X1))
    | ~ m1_subset_1(esk3_2(esk6_0,esk1_2(esk5_0,X1)),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_28]),c_0_29])]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk5_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_50])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_47]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.13/0.39  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.13/0.39  fof(t3_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))&v3_lattice3(X1))=>v3_lattice3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_0)).
% 0.13/0.39  fof(d12_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v3_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_lattice3)).
% 0.13/0.39  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.39  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.13/0.39  fof(c_0_6, plain, ![X9, X10, X11, X12]:((X9=X11|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))&(X10=X12|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.13/0.39  fof(c_0_7, plain, ![X8]:(~l1_orders_2(X8)|m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.13/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))&v3_lattice3(X1))=>v3_lattice3(X2))))), inference(assume_negation,[status(cth)],[t3_yellow_0])).
% 0.13/0.39  cnf(c_0_9, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_10, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  fof(c_0_11, negated_conjecture, (l1_orders_2(esk5_0)&(l1_orders_2(esk6_0)&((g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))=g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))&v3_lattice3(esk5_0))&~v3_lattice3(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.39  cnf(c_0_12, plain, (u1_orders_2(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X3,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.39  cnf(c_0_13, negated_conjecture, (g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))=g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (u1_orders_2(esk5_0)=X1|g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (u1_orders_2(esk5_0)=u1_orders_2(esk6_0)), inference(er,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_17, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(u1_orders_2(esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_16]), c_0_14])])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk6_0))=g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))), inference(rw,[status(thm)],[c_0_13, c_0_16])).
% 0.13/0.39  fof(c_0_20, plain, ![X13, X14, X16, X18]:((((m1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))|~v3_lattice3(X13)|~l1_orders_2(X13))&(r2_lattice3(X13,X14,esk1_2(X13,X14))|~v3_lattice3(X13)|~l1_orders_2(X13)))&(~m1_subset_1(X16,u1_struct_0(X13))|(~r2_lattice3(X13,X14,X16)|r1_orders_2(X13,esk1_2(X13,X14),X16))|~v3_lattice3(X13)|~l1_orders_2(X13)))&((m1_subset_1(esk3_2(X13,X18),u1_struct_0(X13))|(~m1_subset_1(X18,u1_struct_0(X13))|~r2_lattice3(X13,esk2_1(X13),X18))|v3_lattice3(X13)|~l1_orders_2(X13))&((r2_lattice3(X13,esk2_1(X13),esk3_2(X13,X18))|(~m1_subset_1(X18,u1_struct_0(X13))|~r2_lattice3(X13,esk2_1(X13),X18))|v3_lattice3(X13)|~l1_orders_2(X13))&(~r1_orders_2(X13,X18,esk3_2(X13,X18))|(~m1_subset_1(X18,u1_struct_0(X13))|~r2_lattice3(X13,esk2_1(X13),X18))|v3_lattice3(X13)|~l1_orders_2(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (u1_struct_0(esk5_0)=X1|g1_orders_2(u1_struct_0(esk6_0),u1_orders_2(esk6_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.13/0.39  fof(c_0_22, plain, ![X20, X21, X22, X23]:((~r2_lattice3(X20,X21,X22)|(~m1_subset_1(X23,u1_struct_0(X20))|(~r2_hidden(X23,X21)|r1_orders_2(X20,X23,X22)))|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&((m1_subset_1(esk4_3(X20,X21,X22),u1_struct_0(X20))|r2_lattice3(X20,X21,X22)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&((r2_hidden(esk4_3(X20,X21,X22),X21)|r2_lattice3(X20,X21,X22)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))&(~r1_orders_2(X20,esk4_3(X20,X21,X22),X22)|r2_lattice3(X20,X21,X22)|~m1_subset_1(X22,u1_struct_0(X20))|~l1_orders_2(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.39  cnf(c_0_23, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (u1_struct_0(esk5_0)=u1_struct_0(esk6_0)), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (v3_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_26, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_27, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk1_2(esk5_0,X1),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_14])])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (r1_orders_2(esk5_0,X1,X2)|~r2_lattice3(esk5_0,X3,X2)|~r2_hidden(X1,X3)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_14])])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))|m1_subset_1(esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.13/0.39  cnf(c_0_32, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_33, plain, ![X5, X6, X7]:((~r1_orders_2(X5,X6,X7)|r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))&(~r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))|r1_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))|r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X3)|~r2_lattice3(esk5_0,X4,X3)|~r2_hidden(esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X4)|~m1_subset_1(X3,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))|r2_hidden(esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_29])])).
% 0.13/0.39  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))|r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),X3)|~r2_lattice3(esk5_0,X1,X3)|~m1_subset_1(X3,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_38, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk6_0))|~r1_orders_2(esk5_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_16]), c_0_14])]), c_0_24]), c_0_24])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))|r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),esk1_2(esk5_0,X3))|~r2_lattice3(esk5_0,X1,esk1_2(esk5_0,X3))), inference(spm,[status(thm)],[c_0_37, c_0_28])).
% 0.13/0.39  cnf(c_0_41, plain, (r2_lattice3(X1,X2,esk1_2(X1,X2))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk6_0,X1,X2)|~r1_orders_2(esk5_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_29])])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))|r1_orders_2(esk5_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),esk1_2(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_25]), c_0_14])])).
% 0.13/0.39  cnf(c_0_44, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk4_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X2))|r1_orders_2(esk6_0,esk4_3(esk6_0,X1,esk1_2(esk5_0,X2)),esk1_2(esk5_0,X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28])]), c_0_31])).
% 0.13/0.39  cnf(c_0_46, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (r2_lattice3(esk6_0,X1,esk1_2(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_28]), c_0_29])])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (~v3_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (r2_lattice3(esk5_0,X1,X2)|m1_subset_1(esk4_3(esk5_0,X1,X2),u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_14])])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_28]), c_0_29])]), c_0_48])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))|m1_subset_1(esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (r2_lattice3(esk5_0,X1,X2)|r2_hidden(esk4_3(esk5_0,X1,X2),X1)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_14])])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))|r1_orders_2(esk6_0,esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X2)|~r2_lattice3(esk6_0,X3,X2)|~r2_hidden(esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X3)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_51]), c_0_29])])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))|r2_hidden(esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X1)), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (r1_orders_2(esk5_0,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_14])]), c_0_24]), c_0_24])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))|r1_orders_2(esk6_0,esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),X2)|~r2_lattice3(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.39  cnf(c_0_57, plain, (r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_58, plain, (r1_orders_2(X2,esk1_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~v3_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (r1_orders_2(esk5_0,X1,X2)|~r1_orders_2(esk6_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_36]), c_0_29])])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))|r1_orders_2(esk6_0,esk4_3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))|~r2_lattice3(esk6_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))), inference(spm,[status(thm)],[c_0_56, c_0_50])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (r2_lattice3(esk6_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_47]), c_0_28]), c_0_29])]), c_0_48])).
% 0.13/0.39  cnf(c_0_62, plain, (v3_lattice3(X1)|~r1_orders_2(X1,X2,esk3_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (r1_orders_2(esk6_0,esk1_2(esk5_0,X1),X2)|~r2_lattice3(esk5_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_58]), c_0_28]), c_0_25]), c_0_24]), c_0_14])])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (r2_lattice3(esk5_0,X1,X2)|~r1_orders_2(esk6_0,esk4_3(esk5_0,X1,X2),X2)|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_59]), c_0_24]), c_0_14])]), c_0_49])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (r2_lattice3(esk5_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))|r1_orders_2(esk6_0,esk4_3(esk5_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0)))),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (~r2_lattice3(esk5_0,X1,esk3_2(esk6_0,esk1_2(esk5_0,X1)))|~r2_lattice3(esk6_0,esk2_1(esk6_0),esk1_2(esk5_0,X1))|~m1_subset_1(esk3_2(esk6_0,esk1_2(esk5_0,X1)),u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_28]), c_0_29])]), c_0_48])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (r2_lattice3(esk5_0,esk2_1(esk6_0),esk3_2(esk6_0,esk1_2(esk5_0,esk2_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_50])])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_47]), c_0_50])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 69
% 0.13/0.39  # Proof object clause steps            : 56
% 0.13/0.39  # Proof object formula steps           : 13
% 0.13/0.39  # Proof object conjectures             : 43
% 0.13/0.39  # Proof object clause conjectures      : 40
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 20
% 0.13/0.39  # Proof object initial formulas used   : 6
% 0.13/0.39  # Proof object generating inferences   : 35
% 0.13/0.39  # Proof object simplifying inferences  : 68
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 6
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 20
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 20
% 0.13/0.39  # Processed clauses                    : 192
% 0.13/0.39  # ...of these trivial                  : 1
% 0.13/0.39  # ...subsumed                          : 28
% 0.13/0.39  # ...remaining for further processing  : 163
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 6
% 0.13/0.39  # Generated clauses                    : 393
% 0.13/0.39  # ...of the previous two non-trivial   : 377
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 387
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 6
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
% 0.13/0.39  # Current number of processed clauses  : 137
% 0.13/0.39  #    Positive orientable unit clauses  : 27
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 109
% 0.13/0.39  # Current number of unprocessed clauses: 223
% 0.13/0.39  # ...number of literals in the above   : 810
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 26
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1313
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 473
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 19
% 0.13/0.39  # Unit Clause-clause subsumption calls : 104
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 89
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 18025
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.042 s
% 0.13/0.39  # System time              : 0.008 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
