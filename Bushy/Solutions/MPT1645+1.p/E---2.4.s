%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t25_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:46 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 521 expanded)
%              Number of clauses        :   42 ( 215 expanded)
%              Number of leaves         :    6 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 (3191 expanded)
%              Number of equality atoms :   56 ( 793 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',dt_u1_orders_2)).

fof(t25_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( ( v12_waybel_0(X3,X1)
                         => v12_waybel_0(X4,X2) )
                        & ( v13_waybel_0(X3,X1)
                         => v13_waybel_0(X4,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t25_waybel_0)).

fof(t13_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( k3_waybel_0(X1,X3) = k3_waybel_0(X2,X4)
                        & k4_waybel_0(X1,X3) = k4_waybel_0(X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t13_waybel_0)).

fof(t24_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t24_waybel_0)).

fof(t23_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v12_waybel_0(X2,X1)
          <=> r1_tarski(k3_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t25_waybel_0.p',t23_waybel_0)).

fof(c_0_6,plain,(
    ! [X71,X72,X73,X74] :
      ( ( X71 = X73
        | g1_orders_2(X71,X72) != g1_orders_2(X73,X74)
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X71,X71))) )
      & ( X72 = X74
        | g1_orders_2(X71,X72) != g1_orders_2(X73,X74)
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X71,X71))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_7,plain,(
    ! [X52] :
      ( ~ l1_orders_2(X52)
      | m1_subset_1(u1_orders_2(X52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X52)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X3 = X4
                       => ( ( v12_waybel_0(X3,X1)
                           => v12_waybel_0(X4,X2) )
                          & ( v13_waybel_0(X3,X1)
                           => v13_waybel_0(X4,X2) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_waybel_0])).

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
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk3_0 = esk4_0
    & ( v13_waybel_0(esk3_0,esk1_0)
      | v12_waybel_0(esk3_0,esk1_0) )
    & ( ~ v13_waybel_0(esk4_0,esk2_0)
      | v12_waybel_0(esk3_0,esk1_0) )
    & ( v13_waybel_0(esk3_0,esk1_0)
      | ~ v12_waybel_0(esk4_0,esk2_0) )
    & ( ~ v13_waybel_0(esk4_0,esk2_0)
      | ~ v12_waybel_0(esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( u1_orders_2(X1) = u1_orders_2(esk2_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( u1_orders_2(esk2_0) = u1_orders_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])])).

fof(c_0_18,plain,(
    ! [X105,X106,X107,X108] :
      ( ( k3_waybel_0(X105,X107) = k3_waybel_0(X106,X108)
        | X107 != X108
        | ~ m1_subset_1(X108,k1_zfmisc_1(u1_struct_0(X106)))
        | ~ m1_subset_1(X107,k1_zfmisc_1(u1_struct_0(X105)))
        | g1_orders_2(u1_struct_0(X105),u1_orders_2(X105)) != g1_orders_2(u1_struct_0(X106),u1_orders_2(X106))
        | ~ l1_orders_2(X106)
        | ~ l1_orders_2(X105) )
      & ( k4_waybel_0(X105,X107) = k4_waybel_0(X106,X108)
        | X107 != X108
        | ~ m1_subset_1(X108,k1_zfmisc_1(u1_struct_0(X106)))
        | ~ m1_subset_1(X107,k1_zfmisc_1(u1_struct_0(X105)))
        | g1_orders_2(u1_struct_0(X105),u1_orders_2(X105)) != g1_orders_2(u1_struct_0(X106),u1_orders_2(X106))
        | ~ l1_orders_2(X106)
        | ~ l1_orders_2(X105) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_waybel_0])])])])).

cnf(c_0_19,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_21,plain,
    ( k4_waybel_0(X1,X2) = k4_waybel_0(X3,X4)
    | X2 != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk2_0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( k4_waybel_0(X1,X2) = k4_waybel_0(X3,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_15])])).

cnf(c_0_26,plain,
    ( k3_waybel_0(X1,X2) = k3_waybel_0(X3,X4)
    | X2 != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X113,X114] :
      ( ( ~ v13_waybel_0(X114,X113)
        | r1_tarski(k4_waybel_0(X113,X114),X114)
        | ~ m1_subset_1(X114,k1_zfmisc_1(u1_struct_0(X113)))
        | ~ l1_orders_2(X113) )
      & ( ~ r1_tarski(k4_waybel_0(X113,X114),X114)
        | v13_waybel_0(X114,X113)
        | ~ m1_subset_1(X114,k1_zfmisc_1(u1_struct_0(X113)))
        | ~ l1_orders_2(X113) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_waybel_0])])])])).

cnf(c_0_28,negated_conjecture,
    ( k4_waybel_0(esk2_0,X1) = k4_waybel_0(X2,X1)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_24])]),c_0_25]),c_0_25])).

cnf(c_0_29,plain,
    ( k3_waybel_0(X1,X2) = k3_waybel_0(X3,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( v13_waybel_0(X2,X1)
    | ~ r1_tarski(k4_waybel_0(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k4_waybel_0(esk2_0,X1) = k4_waybel_0(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_15])])).

fof(c_0_32,plain,(
    ! [X111,X112] :
      ( ( ~ v12_waybel_0(X112,X111)
        | r1_tarski(k3_waybel_0(X111,X112),X112)
        | ~ m1_subset_1(X112,k1_zfmisc_1(u1_struct_0(X111)))
        | ~ l1_orders_2(X111) )
      & ( ~ r1_tarski(k3_waybel_0(X111,X112),X112)
        | v12_waybel_0(X112,X111)
        | ~ m1_subset_1(X112,k1_zfmisc_1(u1_struct_0(X111)))
        | ~ l1_orders_2(X111) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_waybel_0])])])])).

cnf(c_0_33,negated_conjecture,
    ( k3_waybel_0(esk2_0,X1) = k3_waybel_0(X2,X1)
    | g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_24])]),c_0_25]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v13_waybel_0(X1,esk2_0)
    | ~ r1_tarski(k4_waybel_0(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25]),c_0_24])])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_waybel_0(X2,X1),X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( v12_waybel_0(X2,X1)
    | ~ r1_tarski(k3_waybel_0(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k3_waybel_0(esk2_0,X1) = k3_waybel_0(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_15])])).

cnf(c_0_41,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk1_0)
    | ~ v13_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk1_0)
    | v12_waybel_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( ~ v13_waybel_0(esk4_0,esk2_0)
    | ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( v13_waybel_0(X1,esk2_0)
    | ~ v13_waybel_0(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_15])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v13_waybel_0(esk4_0,esk1_0)
    | ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v12_waybel_0(X1,esk2_0)
    | ~ r1_tarski(k3_waybel_0(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_25]),c_0_24])])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_waybel_0(X2,X1),X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( v12_waybel_0(esk4_0,esk1_0)
    | ~ v13_waybel_0(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( v13_waybel_0(esk4_0,esk1_0)
    | v12_waybel_0(esk4_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_37]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( ~ v12_waybel_0(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v12_waybel_0(X1,esk2_0)
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_15])])).

cnf(c_0_53,negated_conjecture,
    ( v12_waybel_0(esk4_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_45])]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
