%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1525+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (1554 expanded)
%              Number of clauses        :   39 ( 613 expanded)
%              Number of leaves         :    6 ( 367 expanded)
%              Depth                    :   16
%              Number of atoms          :  246 (6572 expanded)
%              Number of equality atoms :   50 (1565 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t3_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & v3_lattice3(X1) )
           => v3_lattice3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X15 = X17
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) )
      & ( X16 = X18
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_7,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | m1_subset_1(u1_orders_2(X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X14)))) ) ),
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
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & l1_orders_2(esk5_0)
    & g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    & v3_lattice3(esk4_0)
    & ~ v3_lattice3(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

fof(c_0_16,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( ~ r2_lattice3(X25,X27,X28)
        | r2_lattice3(X26,X27,X29)
        | X28 != X29
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | g1_orders_2(u1_struct_0(X25),u1_orders_2(X25)) != g1_orders_2(u1_struct_0(X26),u1_orders_2(X26))
        | ~ l1_orders_2(X26)
        | ~ l1_orders_2(X25) )
      & ( ~ r1_lattice3(X25,X27,X28)
        | r1_lattice3(X26,X27,X29)
        | X28 != X29
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | g1_orders_2(u1_struct_0(X25),u1_orders_2(X25)) != g1_orders_2(u1_struct_0(X26),u1_orders_2(X26))
        | ~ l1_orders_2(X26)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_yellow_0])])])])).

fof(c_0_17,plain,(
    ! [X7,X8,X10,X12] :
      ( ( m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | ~ v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X8,esk1_2(X7,X8))
        | ~ v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X8,X10)
        | r1_orders_2(X7,esk1_2(X7,X8),X10)
        | ~ v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk3_2(X7,X12),u1_struct_0(X7))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r2_lattice3(X7,esk2_1(X7),X12)
        | v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,esk2_1(X7),esk3_2(X7,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r2_lattice3(X7,esk2_1(X7),X12)
        | v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X12,esk3_2(X7,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r2_lattice3(X7,esk2_1(X7),X12)
        | v3_lattice3(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_18,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_lattice3(X4,X2,X5)
    | ~ r2_lattice3(X1,X2,X3)
    | X3 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v3_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_18]),c_0_14])])).

cnf(c_0_24,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_25,plain,
    ( r2_lattice3(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r2_lattice3(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_21]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( u1_orders_2(esk4_0) = X1
    | g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk1_2(esk4_0,X2))
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    | ~ r2_lattice3(X3,X1,esk1_2(esk4_0,X2))
    | ~ m1_subset_1(esk1_2(esk4_0,X2),u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( u1_orders_2(esk4_0) = u1_orders_2(esk5_0) ),
    inference(er,[status(thm)],[c_0_28])).

fof(c_0_31,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r1_orders_2(X19,X21,X22)
        | r1_orders_2(X20,X23,X24)
        | X21 != X23
        | X22 != X24
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | g1_orders_2(u1_struct_0(X19),u1_orders_2(X19)) != g1_orders_2(u1_struct_0(X20),u1_orders_2(X20))
        | ~ l1_orders_2(X20)
        | ~ l1_orders_2(X19) )
      & ( ~ r2_orders_2(X19,X21,X22)
        | r2_orders_2(X20,X23,X24)
        | X21 != X23
        | X22 != X24
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | g1_orders_2(u1_struct_0(X19),u1_orders_2(X19)) != g1_orders_2(u1_struct_0(X20),u1_orders_2(X20))
        | ~ l1_orders_2(X20)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_yellow_0])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk1_2(esk4_0,X2))
    | ~ r2_lattice3(esk4_0,X1,esk1_2(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_30]),c_0_26]),c_0_14])])).

cnf(c_0_33,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk5_0,X1,esk1_2(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21]),c_0_14])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v3_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X2,X3)
    | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_26]),c_0_27])]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    | ~ r1_orders_2(X2,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | ~ m1_subset_1(esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))),u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | ~ r1_orders_2(esk4_0,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_18]),c_0_30]),c_0_39]),c_0_14])])).

cnf(c_0_42,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,X2)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    | ~ r2_lattice3(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_24]),c_0_14])])).

cnf(c_0_44,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_2(esk4_0,X1),esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | ~ r2_lattice3(esk4_0,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26]),c_0_18]),c_0_39]),c_0_21]),c_0_14])])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    | ~ r2_lattice3(X2,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | ~ m1_subset_1(esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))),u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_47,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,esk2_1(esk5_0),esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_36]),c_0_26]),c_0_27])]),c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0))))
    | ~ r2_lattice3(esk5_0,X1,esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_39]),c_0_27])])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk5_0,esk2_1(esk5_0),esk3_2(esk5_0,esk1_2(esk4_0,esk2_1(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_36]),c_0_26]),c_0_27])]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),
    [proof]).

%------------------------------------------------------------------------------
