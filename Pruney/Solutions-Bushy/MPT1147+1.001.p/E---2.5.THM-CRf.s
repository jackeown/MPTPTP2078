%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1147+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:49 EST 2020

% Result     : Theorem 0.23s
% Output     : CNFRefutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   77 (35098 expanded)
%              Number of clauses        :   68 (12081 expanded)
%              Number of leaves         :    4 (8195 expanded)
%              Depth                    :   19
%              Number of atoms          :  398 (514456 expanded)
%              Number of equality atoms :   11 (2924 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

fof(c_0_4,negated_conjecture,(
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

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( ( r1_orders_2(X5,X6,X7)
        | ~ r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( X6 != X7
        | ~ r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | X6 = X7
        | r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X19] :
      ( v3_orders_2(esk2_0)
      & v5_orders_2(esk2_0)
      & l1_orders_2(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
      & ( ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
        | r1_orders_2(esk2_0,esk4_0,esk3_0)
        | ~ v6_orders_2(X19,esk2_0)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r2_hidden(esk3_0,X19)
        | ~ r2_hidden(esk4_0,X19) )
      & ( r2_orders_2(esk2_0,esk3_0,esk4_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
        | ~ v6_orders_2(X19,esk2_0)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r2_hidden(esk3_0,X19)
        | ~ r2_hidden(esk4_0,X19) )
      & ( ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
        | v6_orders_2(esk5_0,esk2_0) )
      & ( r1_orders_2(esk2_0,esk4_0,esk3_0)
        | r2_orders_2(esk2_0,esk3_0,esk4_0)
        | v6_orders_2(esk5_0,esk2_0) )
      & ( ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
        | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( r1_orders_2(esk2_0,esk4_0,esk3_0)
        | r2_orders_2(esk2_0,esk3_0,esk4_0)
        | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
        | r2_hidden(esk3_0,esk5_0) )
      & ( r1_orders_2(esk2_0,esk4_0,esk3_0)
        | r2_orders_2(esk2_0,esk3_0,esk4_0)
        | r2_hidden(esk3_0,esk5_0) )
      & ( ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
        | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
        | r2_hidden(esk4_0,esk5_0) )
      & ( r1_orders_2(esk2_0,esk4_0,esk3_0)
        | r2_orders_2(esk2_0,esk3_0,esk4_0)
        | r2_hidden(esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v6_orders_2(X14,X11)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(X12,X14)
        | ~ r2_hidden(X13,X14)
        | r1_orders_2(X11,X12,X13)
        | r1_orders_2(X11,X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( v6_orders_2(esk1_3(X11,X12,X13),X11)
        | ~ r1_orders_2(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r1_orders_2(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(X12,esk1_3(X11,X12,X13))
        | ~ r1_orders_2(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(X13,esk1_3(X11,X12,X13))
        | ~ r1_orders_2(X11,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( v6_orders_2(esk1_3(X11,X12,X13),X11)
        | ~ r1_orders_2(X11,X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r1_orders_2(X11,X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(X12,esk1_3(X11,X12,X13))
        | ~ r1_orders_2(X11,X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(X13,esk1_3(X11,X12,X13))
        | ~ r1_orders_2(X11,X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | ~ v3_orders_2(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).

cnf(c_0_8,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

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

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v6_orders_2(X2,esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_18,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,X1)
    | ~ r2_hidden(X1,esk5_0)
    | ~ v6_orders_2(esk5_0,esk2_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0)
    | v6_orders_2(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0)
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_22,plain,(
    ! [X8,X9,X10] :
      ( ~ v5_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ r1_orders_2(X8,X9,X10)
      | ~ r2_orders_2(X8,X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_21]),c_0_15])])).

cnf(c_0_25,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_15])])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ r2_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_26]),c_0_10])])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_27]),c_0_15])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,plain,
    ( v6_orders_2(esk1_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_9])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_38,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_40,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk4_0,X1)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0))
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_9])])).

cnf(c_0_44,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_9])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0))
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_29]),c_0_9])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_9]),c_0_10])])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_50,plain,
    ( v6_orders_2(esk1_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_15])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_56,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = esk3_0
    | r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk4_0,X1)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_15])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_47]),c_0_9])])).

cnf(c_0_61,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_47]),c_0_9])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_47]),c_0_9])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_26]),c_0_10])])).

cnf(c_0_64,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_65,negated_conjecture,
    ( X1 = esk3_0
    | r2_orders_2(esk2_0,X1,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_15]),c_0_10])])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = esk3_0
    | r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_47]),c_0_15])])).

cnf(c_0_68,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_9])]),c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_15]),c_0_10])])).

cnf(c_0_71,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk3_0,X1)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_69]),c_0_69]),c_0_69])]),c_0_70]),c_0_71])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_69]),c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,esk3_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])]),
    [proof]).

%------------------------------------------------------------------------------
