%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t63_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   67 (1352 expanded)
%              Number of clauses        :   54 ( 506 expanded)
%              Number of leaves         :    6 ( 312 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 (11678 expanded)
%              Number of equality atoms :   10 ( 755 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( X5 = X4
                       => ( ( r1_lattice3(X2,X3,X5)
                           => r1_lattice3(X1,X3,X4) )
                          & ( r2_lattice3(X2,X3,X5)
                           => r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t63_yellow_0.p',t63_yellow_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t63_yellow_0.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t63_yellow_0.p',d9_lattice3)).

fof(t60_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X2,X5,X6) )
                           => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t63_yellow_0.p',t60_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t63_yellow_0.p',dt_m1_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t63_yellow_0.p',d8_lattice3)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ( X5 = X4
                         => ( ( r1_lattice3(X2,X3,X5)
                             => r1_lattice3(X1,X3,X4) )
                            & ( r2_lattice3(X2,X3,X5)
                             => r2_lattice3(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_yellow_0])).

fof(c_0_7,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | m1_subset_1(X39,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & esk5_0 = esk4_0
    & ( r2_lattice3(esk2_0,esk3_0,esk5_0)
      | r1_lattice3(esk2_0,esk3_0,esk5_0) )
    & ( ~ r2_lattice3(esk1_0,esk3_0,esk4_0)
      | r1_lattice3(esk2_0,esk3_0,esk5_0) )
    & ( r2_lattice3(esk2_0,esk3_0,esk5_0)
      | ~ r1_lattice3(esk1_0,esk3_0,esk4_0) )
    & ( ~ r2_lattice3(esk1_0,esk3_0,esk4_0)
      | ~ r1_lattice3(esk1_0,esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X20)
        | r1_orders_2(X19,X22,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( m1_subset_1(esk7_3(X19,X20,X21),u1_struct_0(X19))
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(esk7_3(X19,X20,X21),X20)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r1_orders_2(X19,esk7_3(X19,X20,X21),X21)
        | r2_lattice3(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_10,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ~ l1_orders_2(X45)
      | ~ m1_yellow_0(X46,X45)
      | ~ m1_subset_1(X47,u1_struct_0(X45))
      | ~ m1_subset_1(X48,u1_struct_0(X45))
      | ~ m1_subset_1(X49,u1_struct_0(X46))
      | ~ m1_subset_1(X50,u1_struct_0(X46))
      | X49 != X47
      | X50 != X48
      | ~ r1_orders_2(X46,X49,X50)
      | r1_orders_2(X45,X47,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_yellow_0])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X25,X26] :
      ( ~ l1_orders_2(X25)
      | ~ m1_yellow_0(X26,X25)
      | l1_orders_2(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

fof(c_0_17,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X17,X15)
        | r1_orders_2(X14,X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk6_3(X14,X15,X16),u1_struct_0(X14))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk6_3(X14,X15,X16),X15)
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk6_3(X14,X15,X16))
        | r1_lattice3(X14,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

cnf(c_0_18,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X5 != X3
    | X6 != X4
    | ~ r1_orders_2(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,X1,esk4_0),X1)
    | r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_23,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(X4,X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | m1_subset_1(esk7_3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_0,X1,esk4_0),X1)
    | r1_lattice3(esk1_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_15])])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(X1,X2,esk4_0)
    | ~ r1_orders_2(esk2_0,X2,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk4_0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_3(esk1_0,esk3_0,esk4_0),X1)
    | r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk7_3(esk1_0,esk3_0,esk4_0),X2)
    | ~ r2_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk5_0)
    | r1_lattice3(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,esk5_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0)
    | m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_14]),c_0_15])])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | m1_subset_1(esk7_3(esk1_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_14]),c_0_15])])).

cnf(c_0_42,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk7_3(esk1_0,X1,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_14]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_3(esk1_0,esk3_0,esk4_0),esk4_0)
    | r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk7_3(esk1_0,esk3_0,esk4_0),X1)
    | ~ r2_lattice3(esk2_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk4_0)
    | r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_20]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk6_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk6_3(esk1_0,esk3_0,esk4_0))
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk3_0,esk4_0),X2)
    | ~ r1_lattice3(esk2_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_30])])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk7_3(esk1_0,esk3_0,esk4_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_29]),c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_3(esk1_0,esk3_0,esk4_0),esk4_0)
    | r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_22]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(X1,X2,esk6_3(esk1_0,esk3_0,esk4_0))
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,X2,esk6_3(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(esk6_3(esk1_0,esk3_0,esk4_0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(esk2_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | m1_subset_1(esk6_3(esk1_0,X1,esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_14]),c_0_15])])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk6_3(esk1_0,esk3_0,esk4_0))
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk6_3(esk1_0,esk3_0,esk4_0),X1)
    | ~ r1_lattice3(esk2_0,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_45])).

cnf(c_0_54,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk6_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk5_0)
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk6_3(esk1_0,esk3_0,esk4_0))
    | r1_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk6_3(esk1_0,esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_24]),c_0_15])]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk6_3(esk1_0,esk3_0,esk4_0))
    | r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( r1_lattice3(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk4_0,esk6_3(esk1_0,X1,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_14]),c_0_15])])).

cnf(c_0_59,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_20])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_27]),c_0_14])]),c_0_57]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_62,negated_conjecture,
    ( r2_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_3(esk1_0,esk3_0,esk4_0),esk4_0)
    | ~ r2_hidden(esk7_3(esk1_0,esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_62]),c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk2_0,esk7_3(esk1_0,esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_22]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_65])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
