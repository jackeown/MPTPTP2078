%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t26_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:39 EDT 2019

% Result     : Theorem 0.35s
% Output     : CNFRefutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   71 (3563 expanded)
%              Number of clauses        :   54 (1485 expanded)
%              Number of leaves         :    8 ( 822 expanded)
%              Depth                    :   22
%              Number of atoms          :  339 (12856 expanded)
%              Number of equality atoms :   90 (5409 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   30 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',dt_u1_orders_2)).

fof(t26_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( r1_yellow_0(X1,X3)
               => k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',t26_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',t2_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',dt_k1_yellow_0)).

fof(t14_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( ( r1_yellow_0(X1,X3)
                 => r1_yellow_0(X2,X3) )
                & ( r2_yellow_0(X1,X3)
                 => r2_yellow_0(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',t14_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',d9_yellow_0)).

fof(t1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X4 = X6 )
                             => ( ( r1_orders_2(X1,X3,X4)
                                 => r1_orders_2(X2,X5,X6) )
                                & ( r2_orders_2(X1,X3,X4)
                                 => r2_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t26_yellow_0.p',t1_yellow_0)).

fof(c_0_8,plain,(
    ! [X26,X27,X28,X29] :
      ( ( X26 = X28
        | g1_orders_2(X26,X27) != g1_orders_2(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) )
      & ( X27 = X29
        | g1_orders_2(X26,X27) != g1_orders_2(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_9,plain,(
    ! [X21] :
      ( ~ l1_orders_2(X21)
      | m1_subset_1(u1_orders_2(X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X21)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( r1_yellow_0(X1,X3)
                 => k1_yellow_0(X1,X3) = k1_yellow_0(X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_yellow_0])).

cnf(c_0_11,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & r1_yellow_0(esk1_0,esk3_0)
    & k1_yellow_0(esk1_0,esk3_0) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_14,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk2_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( u1_orders_2(esk2_0) = u1_orders_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17])])).

cnf(c_0_20,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_19])).

fof(c_0_23,plain,(
    ! [X42,X43,X44,X45,X46] :
      ( ( ~ r2_lattice3(X42,X44,X45)
        | r2_lattice3(X43,X44,X46)
        | X45 != X46
        | ~ m1_subset_1(X46,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | g1_orders_2(u1_struct_0(X42),u1_orders_2(X42)) != g1_orders_2(u1_struct_0(X43),u1_orders_2(X43))
        | ~ l1_orders_2(X43)
        | ~ l1_orders_2(X42) )
      & ( ~ r1_lattice3(X42,X44,X45)
        | r1_lattice3(X43,X44,X46)
        | X45 != X46
        | ~ m1_subset_1(X46,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | g1_orders_2(u1_struct_0(X42),u1_orders_2(X42)) != g1_orders_2(u1_struct_0(X43),u1_orders_2(X43))
        | ~ l1_orders_2(X43)
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_yellow_0])])])])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ l1_orders_2(X18)
      | m1_subset_1(k1_yellow_0(X18,X19),u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_21])]),c_0_22])).

cnf(c_0_26,plain,
    ( r2_lattice3(X4,X2,X5)
    | ~ r2_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r2_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])])).

fof(c_0_31,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r1_yellow_0(X33,X35)
        | r1_yellow_0(X34,X35)
        | g1_orders_2(u1_struct_0(X33),u1_orders_2(X33)) != g1_orders_2(u1_struct_0(X34),u1_orders_2(X34))
        | ~ l1_orders_2(X34)
        | ~ l1_orders_2(X33) )
      & ( ~ r2_yellow_0(X33,X35)
        | r2_yellow_0(X34,X35)
        | g1_orders_2(u1_struct_0(X33),u1_orders_2(X33)) != g1_orders_2(u1_struct_0(X34),u1_orders_2(X34))
        | ~ l1_orders_2(X34)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_yellow_0])])])])).

fof(c_0_32,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_lattice3(X11,X12,X13)
        | X13 != k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_lattice3(X11,X12,X14)
        | r1_orders_2(X11,X13,X14)
        | X13 != k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk4_3(X11,X12,X13),u1_struct_0(X11))
        | ~ r2_lattice3(X11,X12,X13)
        | X13 = k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( r2_lattice3(X11,X12,esk4_3(X11,X12,X13))
        | ~ r2_lattice3(X11,X12,X13)
        | X13 = k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) )
      & ( ~ r1_orders_2(X11,X13,esk4_3(X11,X12,X13))
        | ~ r2_lattice3(X11,X12,X13)
        | X13 = k1_yellow_0(X11,X12)
        | ~ r1_yellow_0(X11,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,k1_yellow_0(esk2_0,X2))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ r2_lattice3(X3,X1,k1_yellow_0(esk2_0,X2))
    | ~ m1_subset_1(k1_yellow_0(esk2_0,X2),u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17])])).

cnf(c_0_34,plain,
    ( r1_yellow_0(X3,X2)
    | ~ r1_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,k1_yellow_0(esk2_0,X2))
    | ~ r2_lattice3(esk2_0,X1,k1_yellow_0(esk2_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_19]),c_0_30]),c_0_21])])).

cnf(c_0_38,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_yellow_0(X1,esk3_0)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_17])])).

cnf(c_0_40,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk1_0,X2)
    | m1_subset_1(esk4_3(esk1_0,X2,k1_yellow_0(esk2_0,X1)),u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,X2,k1_yellow_0(esk2_0,X1))
    | ~ r1_yellow_0(esk1_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_17])])).

cnf(c_0_41,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,k1_yellow_0(esk2_0,X2))
    | k1_yellow_0(esk2_0,X2) != k1_yellow_0(esk2_0,X1)
    | ~ r1_yellow_0(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_28]),c_0_30]),c_0_21])])).

cnf(c_0_42,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0)
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_19]),c_0_21])])).

cnf(c_0_43,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk1_0,X2)
    | m1_subset_1(esk4_3(esk1_0,X2,k1_yellow_0(esk2_0,X1)),u1_struct_0(esk1_0))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,X2)
    | ~ r1_yellow_0(esk1_0,X2)
    | ~ r1_yellow_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_yellow_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_22])])).

cnf(c_0_45,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk1_0,esk3_0)
    | m1_subset_1(esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,X1)),u1_struct_0(esk1_0))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,plain,
    ( r2_lattice3(X1,X2,esk4_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_49,plain,(
    ! [X36,X37,X38,X39,X40,X41] :
      ( ( ~ r1_orders_2(X36,X38,X39)
        | r1_orders_2(X37,X40,X41)
        | X38 != X40
        | X39 != X41
        | ~ m1_subset_1(X41,u1_struct_0(X37))
        | ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | g1_orders_2(u1_struct_0(X36),u1_orders_2(X36)) != g1_orders_2(u1_struct_0(X37),u1_orders_2(X37))
        | ~ l1_orders_2(X37)
        | ~ l1_orders_2(X36) )
      & ( ~ r2_orders_2(X36,X38,X39)
        | r2_orders_2(X37,X40,X41)
        | X38 != X40
        | X39 != X41
        | ~ m1_subset_1(X41,u1_struct_0(X37))
        | ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(X36))
        | g1_orders_2(u1_struct_0(X36),u1_orders_2(X36)) != g1_orders_2(u1_struct_0(X37),u1_orders_2(X37))
        | ~ l1_orders_2(X37)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_yellow_0])])])])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | k1_yellow_0(X1,X2) != k1_yellow_0(X1,X4)
    | ~ r2_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ r2_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_19]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk1_0,X2)
    | r2_lattice3(esk1_0,X2,esk4_3(esk1_0,X2,k1_yellow_0(esk2_0,X1)))
    | ~ r2_lattice3(esk1_0,X2,k1_yellow_0(esk2_0,X1))
    | ~ r1_yellow_0(esk1_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_17])])).

cnf(c_0_54,plain,
    ( r1_orders_2(X4,X5,X6)
    | ~ r1_orders_2(X1,X2,X3)
    | X2 != X5
    | X3 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(esk2_0,k1_yellow_0(esk2_0,X1),X2)
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,X3)
    | ~ r2_lattice3(esk2_0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ r1_yellow_0(esk2_0,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_21])])).

cnf(c_0_56,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ r2_lattice3(X2,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)),u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk1_0,X2)
    | r2_lattice3(esk1_0,X2,esk4_3(esk1_0,X2,k1_yellow_0(esk2_0,X1)))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,X2)
    | ~ r1_yellow_0(esk1_0,X2)
    | ~ r1_yellow_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_41])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk2_0,k1_yellow_0(esk2_0,X1),esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,X2)
    | ~ r2_lattice3(esk2_0,X2,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | ~ r1_yellow_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | ~ r2_lattice3(esk1_0,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_52]),c_0_17])])).

cnf(c_0_61,negated_conjecture,
    ( k1_yellow_0(esk2_0,X1) = k1_yellow_0(esk1_0,esk3_0)
    | r2_lattice3(esk1_0,esk3_0,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,X1)))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_44])])).

cnf(c_0_62,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ r1_orders_2(X2,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_52]),c_0_17])])).

cnf(c_0_63,negated_conjecture,
    ( r1_orders_2(esk2_0,k1_yellow_0(esk2_0,X1),esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,X2)
    | ~ r2_lattice3(esk1_0,X2,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | ~ r1_yellow_0(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | ~ r1_orders_2(esk2_0,X1,esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_19]),c_0_52]),c_0_21])])).

cnf(c_0_66,negated_conjecture,
    ( r1_orders_2(esk2_0,k1_yellow_0(esk2_0,X1),esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_44])])).

cnf(c_0_67,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk2_0,X1),esk4_3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)))
    | k1_yellow_0(esk2_0,X1) != k1_yellow_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_30])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_lattice3(esk1_0,esk3_0,k1_yellow_0(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_30]),c_0_35]),c_0_17])]),c_0_47])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_41]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
