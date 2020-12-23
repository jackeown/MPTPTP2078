%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t39_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:20 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   82 (34474 expanded)
%              Number of clauses        :   69 (12081 expanded)
%              Number of leaves         :    6 (8195 expanded)
%              Depth                    :   18
%              Number of atoms          :  412 (479497 expanded)
%              Number of equality atoms :   10 (2920 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   58 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_orders_2,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ? [X4] :
                    ( v6_orders_2(X4,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & r2_hidden(X2,X4)
                    & r2_hidden(X3,X4) )
              <=> ( r2_orders_2(X1,X2,X3)
                <=> ~ r1_orders_2(X1,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t39_orders_2)).

fof(t38_orders_2,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ~ ( ? [X4] :
                        ( v6_orders_2(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X2,X4)
                        & r2_hidden(X3,X4) )
                    & ~ r1_orders_2(X1,X2,X3)
                    & ~ r1_orders_2(X1,X3,X2) )
                & ~ ( ( r1_orders_2(X1,X2,X3)
                      | r1_orders_2(X1,X3,X2) )
                    & ! [X4] :
                        ( ( v6_orders_2(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( r2_hidden(X2,X4)
                            & r2_hidden(X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t38_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t4_subset)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',d10_orders_2)).

fof(t30_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r1_orders_2(X1,X2,X3)
                  & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t30_orders_2)).

fof(irreflexivity_r2_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ~ r2_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',irreflexivity_r2_orders_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ? [X4] :
                      ( v6_orders_2(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                      & r2_hidden(X2,X4)
                      & r2_hidden(X3,X4) )
                <=> ( r2_orders_2(X1,X2,X3)
                  <=> ~ r1_orders_2(X1,X3,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_orders_2])).

fof(c_0_7,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ v6_orders_2(X33,X30)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(X31,X33)
        | ~ r2_hidden(X32,X33)
        | r1_orders_2(X30,X31,X32)
        | r1_orders_2(X30,X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( v6_orders_2(esk8_3(X30,X31,X32),X30)
        | ~ r1_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk8_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r1_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(X31,esk8_3(X30,X31,X32))
        | ~ r1_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(X32,esk8_3(X30,X31,X32))
        | ~ r1_orders_2(X30,X31,X32)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( v6_orders_2(esk8_3(X30,X31,X32),X30)
        | ~ r1_orders_2(X30,X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( m1_subset_1(esk8_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r1_orders_2(X30,X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(X31,esk8_3(X30,X31,X32))
        | ~ r1_orders_2(X30,X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(X32,esk8_3(X30,X31,X32))
        | ~ r1_orders_2(X30,X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ v3_orders_2(X30)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).

fof(c_0_8,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | m1_subset_1(X37,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ( r1_orders_2(X12,X13,X14)
        | ~ r2_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( X13 != X14
        | ~ r2_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r1_orders_2(X12,X13,X14)
        | X13 = X14
        | r2_orders_2(X12,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X8] :
      ( v3_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
      & ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
        | r1_orders_2(esk1_0,esk3_0,esk2_0)
        | ~ v6_orders_2(X8,esk1_0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X8)
        | ~ r2_hidden(esk3_0,X8) )
      & ( r2_orders_2(esk1_0,esk2_0,esk3_0)
        | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
        | ~ v6_orders_2(X8,esk1_0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X8)
        | ~ r2_hidden(esk3_0,X8) )
      & ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
        | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
        | v6_orders_2(esk4_0,esk1_0) )
      & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_orders_2(esk1_0,esk2_0,esk3_0)
        | v6_orders_2(esk4_0,esk1_0) )
      & ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
        | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
        | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
      & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_orders_2(esk1_0,esk2_0,esk3_0)
        | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
      & ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
        | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_hidden(esk2_0,esk4_0) )
      & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_orders_2(esk1_0,esk2_0,esk3_0)
        | r2_hidden(esk2_0,esk4_0) )
      & ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
        | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_hidden(esk3_0,esk4_0) )
      & ( r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_orders_2(esk1_0,esk2_0,esk3_0)
        | r2_hidden(esk3_0,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

cnf(c_0_11,plain,
    ( r1_orders_2(X2,X3,X4)
    | r1_orders_2(X2,X4,X3)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,X2,X3)
    | r1_orders_2(X1,X3,X2)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X2,X4)
    | ~ v6_orders_2(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0)
    | v6_orders_2(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r2_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,X1,X2)
    | r1_orders_2(esk1_0,X2,X1)
    | r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_15]),c_0_18])]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( ~ v5_orders_2(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | ~ r1_orders_2(X27,X28,X29)
      | ~ r2_orders_2(X27,X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,X1,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,X1)
    | r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_25]),c_0_22])])).

cnf(c_0_29,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r2_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_15]),c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_31]),c_0_22])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,esk8_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( v6_orders_2(esk8_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,esk8_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,negated_conjecture,
    ( r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_14])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk8_3(esk1_0,esk3_0,X1))
    | ~ r1_orders_2(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_14]),c_0_15]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_15]),c_0_18])])).

cnf(c_0_42,negated_conjecture,
    ( v6_orders_2(esk8_3(esk1_0,X1,esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_15]),c_0_18])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk8_3(esk1_0,X1,esk2_0))
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_15]),c_0_18])])).

cnf(c_0_44,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1)
    | ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk2_0,esk8_3(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_22])])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | m1_subset_1(esk8_3(esk1_0,esk3_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_14])])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | v6_orders_2(esk8_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_14])])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk3_0,esk8_3(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_14])])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk3_0
    | r2_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_14]),c_0_15])])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,esk8_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,esk8_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_54,plain,
    ( v6_orders_2(esk8_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk8_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_22])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,esk8_3(esk1_0,esk3_0,X1))
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_14]),c_0_15]),c_0_18])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,esk8_3(esk1_0,X1,esk2_0))
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_22]),c_0_15]),c_0_18])])).

cnf(c_0_60,negated_conjecture,
    ( v6_orders_2(esk8_3(esk1_0,X1,esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_22]),c_0_15]),c_0_18])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,X1,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_22]),c_0_15]),c_0_18])])).

fof(c_0_62,plain,(
    ! [X20,X21,X22] :
      ( ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_subset_1(X22,u1_struct_0(X20))
      | ~ r2_orders_2(X20,X21,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = esk2_0
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1)
    | ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_0,esk8_3(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_22])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,esk8_3(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_51]),c_0_14])])).

cnf(c_0_66,negated_conjecture,
    ( v6_orders_2(esk8_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_51]),c_0_14])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk3_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_51]),c_0_14])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r2_orders_2(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_15]),c_0_30])])).

cnf(c_0_69,plain,
    ( ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( X1 = esk2_0
    | r2_orders_2(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_22]),c_0_15])])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 = esk2_0
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_67])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_51]),c_0_22])])).

cnf(c_0_73,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(condense,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_14])]),c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_22]),c_0_15])])).

cnf(c_0_76,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk2_0,X1)
    | ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_74]),c_0_74]),c_0_74])]),c_0_75]),c_0_76])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_0,esk8_3(esk1_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_74]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( v6_orders_2(esk8_3(esk1_0,esk2_0,esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk8_3(esk1_0,esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
