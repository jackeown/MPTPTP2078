%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t13_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:36 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 (1312 expanded)
%              Number of clauses        :   44 ( 559 expanded)
%              Number of leaves         :    7 ( 307 expanded)
%              Depth                    :   14
%              Number of atoms          :  217 (5838 expanded)
%              Number of equality atoms :   40 (1320 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t13_yellow_0.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t13_yellow_0.p',dt_u1_orders_2)).

fof(t13_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ( ( v1_yellow_0(X1)
               => v1_yellow_0(X2) )
              & ( v2_yellow_0(X1)
               => v2_yellow_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t13_yellow_0.p',t13_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t13_yellow_0.p',t3_subset)).

fof(t2_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3,X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X2))
                   => ( X4 = X5
                     => ( ( r2_lattice3(X1,X3,X4)
                         => r2_lattice3(X2,X3,X5) )
                        & ( r1_lattice3(X1,X3,X4)
                         => r1_lattice3(X2,X3,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t13_yellow_0.p',t2_yellow_0)).

fof(d5_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r2_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t13_yellow_0.p',d5_yellow_0)).

fof(d4_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_yellow_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & r1_lattice3(X1,u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t13_yellow_0.p',d4_yellow_0)).

fof(c_0_7,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X23 = X25
        | g1_orders_2(X23,X24) != g1_orders_2(X25,X26)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) )
      & ( X24 = X26
        | g1_orders_2(X23,X24) != g1_orders_2(X25,X26)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_8,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | m1_subset_1(u1_orders_2(X18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X18)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ( ( v1_yellow_0(X1)
                 => v1_yellow_0(X2) )
                & ( v2_yellow_0(X1)
                 => v2_yellow_0(X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_0])).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & ( v2_yellow_0(esk1_0)
      | v1_yellow_0(esk1_0) )
    & ( ~ v2_yellow_0(esk2_0)
      | v1_yellow_0(esk1_0) )
    & ( v2_yellow_0(esk1_0)
      | ~ v1_yellow_0(esk2_0) )
    & ( ~ v2_yellow_0(esk2_0)
      | ~ v1_yellow_0(esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_13,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X32,k1_zfmisc_1(X33))
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | m1_subset_1(X32,k1_zfmisc_1(X33)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( u1_orders_2(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(u1_orders_2(X1),k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( u1_orders_2(esk1_0) = u1_orders_2(esk2_0) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(u1_orders_2(esk2_0),k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16])])).

cnf(c_0_25,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_22])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r2_lattice3(X27,X29,X30)
        | r2_lattice3(X28,X29,X31)
        | X30 != X31
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | g1_orders_2(u1_struct_0(X27),u1_orders_2(X27)) != g1_orders_2(u1_struct_0(X28),u1_orders_2(X28))
        | ~ l1_orders_2(X28)
        | ~ l1_orders_2(X27) )
      & ( ~ r1_lattice3(X27,X29,X30)
        | r1_lattice3(X28,X29,X31)
        | X30 != X31
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | g1_orders_2(u1_struct_0(X27),u1_orders_2(X27)) != g1_orders_2(u1_struct_0(X28),u1_orders_2(X28))
        | ~ l1_orders_2(X28)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_yellow_0])])])])).

fof(c_0_27,plain,(
    ! [X12,X14] :
      ( ( m1_subset_1(esk4_1(X12),u1_struct_0(X12))
        | ~ v2_yellow_0(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_lattice3(X12,u1_struct_0(X12),esk4_1(X12))
        | ~ v2_yellow_0(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ r2_lattice3(X12,u1_struct_0(X12),X14)
        | v2_yellow_0(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_yellow_0])])])])])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_29,plain,(
    ! [X9,X11] :
      ( ( m1_subset_1(esk3_1(X9),u1_struct_0(X9))
        | ~ v1_yellow_0(X9)
        | ~ l1_orders_2(X9) )
      & ( r1_lattice3(X9,u1_struct_0(X9),esk3_1(X9))
        | ~ v1_yellow_0(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ r1_lattice3(X9,u1_struct_0(X9),X11)
        | v1_yellow_0(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_yellow_0])])])])])).

cnf(c_0_30,plain,
    ( r2_lattice3(X4,X2,X5)
    | ~ r2_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r2_lattice3(X1,u1_struct_0(X1),esk4_1(X1))
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(X1))
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_lattice3(X4,X2,X5)
    | ~ r1_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_lattice3(X1,u1_struct_0(X1),esk3_1(X1))
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk1_0,u1_struct_0(esk2_0),esk4_1(esk1_0))
    | ~ v2_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_1(esk1_0),u1_struct_0(esk2_0))
    | ~ v2_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_16])])).

cnf(c_0_40,plain,
    ( r1_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_lattice3(esk1_0,u1_struct_0(esk2_0),esk3_1(esk1_0))
    | ~ v1_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_16])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk3_1(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_yellow_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_16])])).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(X1,u1_struct_0(esk2_0),esk4_1(esk1_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ m1_subset_1(esk4_1(esk1_0),u1_struct_0(X1))
    | ~ v2_yellow_0(esk1_0)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_32]),c_0_22]),c_0_32]),c_0_16])]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( r1_lattice3(X1,u1_struct_0(esk2_0),esk3_1(esk1_0))
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ m1_subset_1(esk3_1(esk1_0),u1_struct_0(X1))
    | ~ v1_yellow_0(esk1_0)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32]),c_0_22]),c_0_32]),c_0_16])]),c_0_42])).

cnf(c_0_46,plain,
    ( v2_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,u1_struct_0(X2),X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk2_0,u1_struct_0(esk2_0),esk4_1(esk1_0))
    | ~ v2_yellow_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_44])]),c_0_39])).

cnf(c_0_48,plain,
    ( v1_yellow_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,u1_struct_0(X2),X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( r1_lattice3(esk2_0,u1_struct_0(esk2_0),esk3_1(esk1_0))
    | ~ v1_yellow_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_44])]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v2_yellow_0(esk2_0)
    | ~ v2_yellow_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_44])]),c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( v2_yellow_0(esk1_0)
    | v1_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( v1_yellow_0(esk1_0)
    | ~ v2_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( v2_yellow_0(esk1_0)
    | ~ v1_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_yellow_0(esk2_0)
    | ~ v1_yellow_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,negated_conjecture,
    ( v1_yellow_0(esk2_0)
    | ~ v1_yellow_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_44])]),c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( v1_yellow_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_yellow_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_53]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
