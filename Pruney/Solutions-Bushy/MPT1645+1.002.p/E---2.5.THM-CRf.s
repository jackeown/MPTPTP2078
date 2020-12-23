%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1645+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 289 expanded)
%              Number of clauses        :   34 ( 106 expanded)
%              Number of leaves         :    4 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 (2225 expanded)
%              Number of equality atoms :   34 ( 411 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

fof(t24_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(t23_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v12_waybel_0(X2,X1)
          <=> r1_tarski(k3_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_0)).

fof(c_0_4,plain,(
    ! [X24,X25,X26,X27] :
      ( ( k3_waybel_0(X24,X26) = k3_waybel_0(X25,X27)
        | X26 != X27
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | g1_orders_2(u1_struct_0(X24),u1_orders_2(X24)) != g1_orders_2(u1_struct_0(X25),u1_orders_2(X25))
        | ~ l1_orders_2(X25)
        | ~ l1_orders_2(X24) )
      & ( k4_waybel_0(X24,X26) = k4_waybel_0(X25,X27)
        | X26 != X27
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | g1_orders_2(u1_struct_0(X24),u1_orders_2(X24)) != g1_orders_2(u1_struct_0(X25),u1_orders_2(X25))
        | ~ l1_orders_2(X25)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_waybel_0])])])])).

fof(c_0_5,negated_conjecture,(
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

cnf(c_0_6,plain,
    ( k4_waybel_0(X1,X2) = k4_waybel_0(X3,X4)
    | X2 != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk7_0)
    & l1_orders_2(esk8_0)
    & g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0)) = g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk8_0)))
    & esk9_0 = esk10_0
    & ( v13_waybel_0(esk9_0,esk7_0)
      | v12_waybel_0(esk9_0,esk7_0) )
    & ( ~ v13_waybel_0(esk10_0,esk8_0)
      | v12_waybel_0(esk9_0,esk7_0) )
    & ( v13_waybel_0(esk9_0,esk7_0)
      | ~ v12_waybel_0(esk10_0,esk8_0) )
    & ( ~ v13_waybel_0(esk10_0,esk8_0)
      | ~ v12_waybel_0(esk10_0,esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( k4_waybel_0(X1,X2) = k4_waybel_0(X3,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0)) = g1_orders_2(u1_struct_0(esk8_0),u1_orders_2(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_waybel_0(X1,X2) = k3_waybel_0(X3,X4)
    | X2 != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_12,plain,(
    ! [X30,X31] :
      ( ( ~ v13_waybel_0(X31,X30)
        | r1_tarski(k4_waybel_0(X30,X31),X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) )
      & ( ~ r1_tarski(k4_waybel_0(X30,X31),X31)
        | v13_waybel_0(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_waybel_0])])])])).

cnf(c_0_13,negated_conjecture,
    ( k4_waybel_0(X1,X2) = k4_waybel_0(esk8_0,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( k3_waybel_0(X1,X2) = k3_waybel_0(X3,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v13_waybel_0(X2,X1)
    | ~ r1_tarski(k4_waybel_0(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k4_waybel_0(esk8_0,X1) = k4_waybel_0(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14])])).

fof(c_0_18,plain,(
    ! [X28,X29] :
      ( ( ~ v12_waybel_0(X29,X28)
        | r1_tarski(k3_waybel_0(X28,X29),X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_orders_2(X28) )
      & ( ~ r1_tarski(k3_waybel_0(X28,X29),X29)
        | v12_waybel_0(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_waybel_0])])])])).

cnf(c_0_19,negated_conjecture,
    ( k3_waybel_0(X1,X2) = k3_waybel_0(esk8_0,X2)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(esk7_0),u1_orders_2(esk7_0))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_9]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( v13_waybel_0(X1,esk8_0)
    | ~ r1_tarski(k4_waybel_0(esk7_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_10])])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_waybel_0(X2,X1),X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( v13_waybel_0(esk9_0,esk7_0)
    | ~ v12_waybel_0(esk10_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( v12_waybel_0(X2,X1)
    | ~ r1_tarski(k3_waybel_0(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k3_waybel_0(esk8_0,X1) = k3_waybel_0(esk7_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( ~ v13_waybel_0(esk10_0,esk8_0)
    | ~ v12_waybel_0(esk10_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( v13_waybel_0(X1,esk8_0)
    | ~ v13_waybel_0(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v13_waybel_0(esk10_0,esk7_0)
    | ~ v12_waybel_0(esk10_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v12_waybel_0(X1,esk8_0)
    | ~ r1_tarski(k3_waybel_0(esk7_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_10])])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_waybel_0(X2,X1),X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v13_waybel_0(esk9_0,esk7_0)
    | v12_waybel_0(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( ~ v12_waybel_0(esk10_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v12_waybel_0(X1,esk8_0)
    | ~ v12_waybel_0(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk8_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_14])])).

cnf(c_0_37,negated_conjecture,
    ( v12_waybel_0(esk9_0,esk7_0)
    | ~ v13_waybel_0(esk10_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,negated_conjecture,
    ( v13_waybel_0(esk10_0,esk7_0)
    | v12_waybel_0(esk10_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_23]),c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( ~ v12_waybel_0(esk10_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29]),c_0_30])])).

cnf(c_0_40,negated_conjecture,
    ( v12_waybel_0(esk10_0,esk7_0)
    | ~ v13_waybel_0(esk10_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( v13_waybel_0(esk10_0,esk7_0) ),
    inference(sr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29]),c_0_30])]),c_0_41])]),c_0_39]),
    [proof]).

%------------------------------------------------------------------------------
