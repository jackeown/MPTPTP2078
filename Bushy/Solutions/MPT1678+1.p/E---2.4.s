%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t58_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:00 EDT 2019

% Result     : Theorem 142.75s
% Output     : CNFRefutation 142.75s
% Verified   : 
% Statistics : Number of formulae       :   41 (2178 expanded)
%              Number of clauses        :   32 ( 586 expanded)
%              Number of leaves         :    4 ( 796 expanded)
%              Depth                    :   14
%              Number of atoms          :  230 (24213 expanded)
%              Number of equality atoms :    9 (2232 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r2_yellow_0(X1,X5)
                                  & X4 = k2_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                    <=> r1_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t58_waybel_0.p',t57_waybel_0)).

fof(t58_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r2_yellow_0(X1,X5)
                                  & X4 = k2_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) )
               => ( r2_yellow_0(X1,X2)
                <=> r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t58_waybel_0.p',t58_waybel_0)).

fof(t48_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) )
            & r2_yellow_0(X1,X2) )
         => r2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t58_waybel_0.p',t48_yellow_0)).

fof(c_0_3,plain,(
    ! [X2,X3,X1] :
      ( epred1_3(X1,X3,X2)
    <=> ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) ) ) ),
    introduced(definition)).

fof(c_0_4,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( epred1_3(X1,X3,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                    <=> r1_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t57_waybel_0,c_0_3])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( epred1_3(X1,X3,X2)
                 => ( r2_yellow_0(X1,X2)
                  <=> r2_yellow_0(X1,X3) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t58_waybel_0]),c_0_3])).

fof(c_0_6,plain,(
    ! [X94,X95,X96,X97] :
      ( ( ~ r1_lattice3(X94,X95,X97)
        | r1_lattice3(X94,X96,X97)
        | ~ m1_subset_1(X97,u1_struct_0(X94))
        | ~ epred1_3(X94,X96,X95)
        | ~ m1_subset_1(X96,k1_zfmisc_1(u1_struct_0(X94)))
        | ~ m1_subset_1(X95,k1_zfmisc_1(u1_struct_0(X94)))
        | v2_struct_0(X94)
        | ~ v3_orders_2(X94)
        | ~ v4_orders_2(X94)
        | ~ l1_orders_2(X94) )
      & ( ~ r1_lattice3(X94,X96,X97)
        | r1_lattice3(X94,X95,X97)
        | ~ m1_subset_1(X97,u1_struct_0(X94))
        | ~ epred1_3(X94,X96,X95)
        | ~ m1_subset_1(X96,k1_zfmisc_1(u1_struct_0(X94)))
        | ~ m1_subset_1(X95,k1_zfmisc_1(u1_struct_0(X94)))
        | v2_struct_0(X94)
        | ~ v3_orders_2(X94)
        | ~ v4_orders_2(X94)
        | ~ l1_orders_2(X94) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & epred1_3(esk1_0,esk3_0,esk2_0)
    & ( ~ r2_yellow_0(esk1_0,esk2_0)
      | ~ r2_yellow_0(esk1_0,esk3_0) )
    & ( r2_yellow_0(esk1_0,esk2_0)
      | r2_yellow_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X1,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X87,X88,X89] :
      ( ( m1_subset_1(esk23_3(X87,X88,X89),u1_struct_0(X87))
        | ~ r2_yellow_0(X87,X88)
        | r2_yellow_0(X87,X89)
        | v2_struct_0(X87)
        | ~ l1_orders_2(X87) )
      & ( ~ r1_lattice3(X87,X88,esk23_3(X87,X88,X89))
        | ~ r1_lattice3(X87,X89,esk23_3(X87,X88,X89))
        | ~ r2_yellow_0(X87,X88)
        | r2_yellow_0(X87,X89)
        | v2_struct_0(X87)
        | ~ l1_orders_2(X87) )
      & ( r1_lattice3(X87,X88,esk23_3(X87,X88,X89))
        | r1_lattice3(X87,X89,esk23_3(X87,X88,X89))
        | ~ r2_yellow_0(X87,X88)
        | r2_yellow_0(X87,X89)
        | v2_struct_0(X87)
        | ~ l1_orders_2(X87) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_yellow_0])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,X1)
    | ~ epred1_3(esk1_0,esk3_0,X2)
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( epred1_3(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r1_lattice3(X1,X2,esk23_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk23_3(X1,X2,X3))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk2_0)
    | r2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk23_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,X1)
    | ~ r1_lattice3(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,esk23_3(esk1_0,esk2_0,X1))
    | r1_lattice3(esk1_0,X1,esk23_3(esk1_0,esk2_0,X1))
    | r2_yellow_0(esk1_0,esk3_0)
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10])]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0)
    | r2_yellow_0(esk1_0,X1)
    | m1_subset_1(esk23_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_10])]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk23_3(esk1_0,esk2_0,X1))
    | r1_lattice3(esk1_0,X1,esk23_3(esk1_0,esk2_0,X1))
    | r2_yellow_0(esk1_0,esk3_0)
    | r2_yellow_0(esk1_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_25,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X1,X2,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk23_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk23_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk23_3(esk1_0,esk2_0,esk3_0))
    | r2_yellow_0(esk1_0,esk3_0) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,X1)
    | ~ epred1_3(esk1_0,X2,esk2_0)
    | ~ r1_lattice3(esk1_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0)
    | ~ r1_lattice3(esk1_0,esk2_0,esk23_3(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_10])]),c_0_13]),c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r1_lattice3(esk1_0,esk2_0,X1)
    | ~ r1_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_9]),c_0_17])])).

cnf(c_0_31,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0)
    | ~ m1_subset_1(esk23_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,esk2_0)
    | ~ r2_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk23_3(esk1_0,esk3_0,X1))
    | r1_lattice3(esk1_0,X1,esk23_3(esk1_0,esk3_0,X1))
    | r2_yellow_0(esk1_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_33]),c_0_10])]),c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,esk3_0,esk23_3(esk1_0,X1,esk2_0))
    | ~ r1_lattice3(esk1_0,X1,esk23_3(esk1_0,X1,esk2_0))
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ m1_subset_1(esk23_3(esk1_0,X1,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_10])]),c_0_13]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk23_3(esk1_0,esk3_0,esk2_0))
    | ~ m1_subset_1(esk23_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_35]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(esk23_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33])]),c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( r2_yellow_0(esk1_0,X1)
    | m1_subset_1(esk23_3(esk1_0,esk3_0,X1),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_33]),c_0_10])]),c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
