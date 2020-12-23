%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 (30074 expanded)
%              Number of clauses        :   65 (10369 expanded)
%              Number of leaves         :    4 (7019 expanded)
%              Depth                    :   18
%              Number of atoms          :  394 (442116 expanded)
%              Number of equality atoms :   14 (2604 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

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

cnf(c_0_22,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,X1)
    | r1_orders_2(esk2_0,X1,esk4_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_21]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( v6_orders_2(esk1_3(X1,X2,X3),X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,esk1_3(X2,X1,X3))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk2_0,esk4_0,esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_24]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_33,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_35,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk4_0,X1)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0))
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_15])])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_9])])).

cnf(c_0_38,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0)
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_9])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0))
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_9])])).

fof(c_0_40,plain,(
    ! [X8,X9,X10] :
      ( ~ v5_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ r1_orders_2(X8,X9,X10)
      | ~ r1_orders_2(X8,X10,X9)
      | X9 = X10 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_41,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0)
    | r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_43,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_9]),c_0_10])])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_42]),c_0_15])])).

cnf(c_0_47,negated_conjecture,
    ( X1 = esk3_0
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_15]),c_0_44]),c_0_10])])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_15])])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r1_orders_2(esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_9])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))
    | ~ r1_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_57,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_orders_2(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_15]),c_0_12]),c_0_10])])).

cnf(c_0_59,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk4_0,X1)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_46]),c_0_15])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_46]),c_0_9])])).

cnf(c_0_63,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_9])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_46]),c_0_9])])).

cnf(c_0_65,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_15]),c_0_10])])).

cnf(c_0_68,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk3_0,X1)
    | ~ v6_orders_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_66]),c_0_66]),c_0_66])]),c_0_67]),c_0_68])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_66]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v6_orders_2(esk1_3(esk2_0,esk3_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:11:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.40  # and selection function SelectNewComplexAHPNS.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.051 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t39_orders_2, conjecture, ![X1]:(((v3_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(?[X4]:(((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))&r2_hidden(X2,X4))&r2_hidden(X3,X4))<=>(r2_orders_2(X1,X2,X3)<=>~(r1_orders_2(X1,X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_orders_2)).
% 0.19/0.40  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 0.19/0.40  fof(t38_orders_2, axiom, ![X1]:((v3_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(~(((?[X4]:(((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))&r2_hidden(X2,X4))&r2_hidden(X3,X4))&~(r1_orders_2(X1,X2,X3)))&~(r1_orders_2(X1,X3,X2))))&~(((r1_orders_2(X1,X2,X3)|r1_orders_2(X1,X3,X2))&![X4]:((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~((r2_hidden(X2,X4)&r2_hidden(X3,X4)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_orders_2)).
% 0.19/0.40  fof(t25_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X2))=>X2=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 0.19/0.40  fof(c_0_4, negated_conjecture, ~(![X1]:(((v3_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(?[X4]:(((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))&r2_hidden(X2,X4))&r2_hidden(X3,X4))<=>(r2_orders_2(X1,X2,X3)<=>~(r1_orders_2(X1,X3,X2)))))))), inference(assume_negation,[status(cth)],[t39_orders_2])).
% 0.19/0.40  fof(c_0_5, plain, ![X5, X6, X7]:(((r1_orders_2(X5,X6,X7)|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))&(X6!=X7|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5)))&(~r1_orders_2(X5,X6,X7)|X6=X7|r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.19/0.40  fof(c_0_6, negated_conjecture, ![X19]:(((v3_orders_2(esk2_0)&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(((~r2_orders_2(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)|(~v6_orders_2(X19,esk2_0)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X19)|~r2_hidden(esk4_0,X19)))&(r2_orders_2(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|(~v6_orders_2(X19,esk2_0)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X19)|~r2_hidden(esk4_0,X19))))&(((((~r2_orders_2(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|v6_orders_2(esk5_0,esk2_0))&(r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|v6_orders_2(esk5_0,esk2_0)))&((~r2_orders_2(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))))&(r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))))))&((~r2_orders_2(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_hidden(esk3_0,esk5_0))&(r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|r2_hidden(esk3_0,esk5_0))))&((~r2_orders_2(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_hidden(esk4_0,esk5_0))&(r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|r2_hidden(esk4_0,esk5_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).
% 0.19/0.40  fof(c_0_7, plain, ![X11, X12, X13, X14]:((~v6_orders_2(X14,X11)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X11)))|~r2_hidden(X12,X14)|~r2_hidden(X13,X14)|r1_orders_2(X11,X12,X13)|r1_orders_2(X11,X13,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11)))&((((v6_orders_2(esk1_3(X11,X12,X13),X11)|~r1_orders_2(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11)))&(m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X11)))|~r1_orders_2(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11))))&((r2_hidden(X12,esk1_3(X11,X12,X13))|~r1_orders_2(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11)))&(r2_hidden(X13,esk1_3(X11,X12,X13))|~r1_orders_2(X11,X12,X13)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11)))))&(((v6_orders_2(esk1_3(X11,X12,X13),X11)|~r1_orders_2(X11,X13,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11)))&(m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X11)))|~r1_orders_2(X11,X13,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11))))&((r2_hidden(X12,esk1_3(X11,X12,X13))|~r1_orders_2(X11,X13,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11)))&(r2_hidden(X13,esk1_3(X11,X12,X13))|~r1_orders_2(X11,X13,X12)|~m1_subset_1(X13,u1_struct_0(X11))|~m1_subset_1(X12,u1_struct_0(X11))|(~v3_orders_2(X11)|~l1_orders_2(X11))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).
% 0.19/0.40  cnf(c_0_8, plain, (r1_orders_2(X1,X2,X3)|~r2_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_11, plain, (r1_orders_2(X2,X3,X4)|r1_orders_2(X2,X4,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~r2_hidden(X4,X1)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_12, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_13, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r2_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.19/0.40  cnf(c_0_14, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_16, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|~r2_hidden(esk4_0,X2)|~r2_hidden(X1,X2)|~v6_orders_2(X2,esk2_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_9]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)|r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)|r1_orders_2(esk2_0,X1,esk4_0)|r1_orders_2(esk2_0,esk4_0,X1)|~r2_hidden(X1,esk5_0)|~v6_orders_2(esk5_0,esk2_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|v6_orders_2(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk3_0)|r1_orders_2(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,X1)|r1_orders_2(esk2_0,X1,esk4_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)|r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_21]), c_0_15])])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)|r1_orders_2(esk2_0,esk4_0,esk3_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])])).
% 0.19/0.40  cnf(c_0_25, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_26, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_27, plain, (v6_orders_2(esk1_3(X1,X2,X3),X1)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_28, plain, (r2_hidden(X1,esk1_3(X2,X1,X3))|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (r2_orders_2(esk2_0,esk3_0,esk4_0)|~r1_orders_2(esk2_0,esk4_0,esk3_0)|~v6_orders_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r2_hidden(esk4_0,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk3_0)|r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_24]), c_0_15])])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))|~r1_orders_2(esk2_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_9]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_15]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_15]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)|~r2_hidden(esk3_0,X1)|~r2_hidden(esk4_0,X1)|~v6_orders_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0))|r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_15])])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_9])])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0)|r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_9])])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0))|r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_9])])).
% 0.19/0.40  fof(c_0_40, plain, ![X8, X9, X10]:(~v5_orders_2(X8)|~l1_orders_2(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|(~r1_orders_2(X8,X9,X10)|~r1_orders_2(X8,X10,X9)|X9=X10)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).
% 0.19/0.40  cnf(c_0_41, plain, (X2=X3|r2_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)|r2_orders_2(esk2_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.40  cnf(c_0_43, plain, (X2=X3|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (X1=esk4_0|r2_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_9]), c_0_10])])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_42]), c_0_15])])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (X1=esk3_0|~r1_orders_2(esk2_0,esk3_0,X1)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_15]), c_0_44]), c_0_10])])).
% 0.19/0.40  cnf(c_0_48, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_49, plain, (r2_hidden(X1,esk1_3(X2,X1,X3))|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_50, plain, (v6_orders_2(esk1_3(X1,X2,X3),X1)|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_51, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (r1_orders_2(esk2_0,esk4_0,esk3_0)|~r2_orders_2(esk2_0,esk3_0,esk4_0)|~v6_orders_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)|~r2_hidden(esk4_0,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (esk4_0=esk3_0|r2_orders_2(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_15])])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (esk4_0=esk3_0|~r1_orders_2(esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_9])])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk4_0,X1))|~r1_orders_2(esk2_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_9]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,X1,esk3_0))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_15]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,X1,esk3_0),esk2_0)|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_15]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_orders_2(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_15]), c_0_12]), c_0_10])])).
% 0.19/0.40  cnf(c_0_59, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (esk4_0=esk3_0|~r2_hidden(esk3_0,X1)|~r2_hidden(esk4_0,X1)|~v6_orders_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_0,esk1_3(esk2_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_46]), c_0_15])])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (r2_hidden(esk4_0,esk1_3(esk2_0,esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_46]), c_0_9])])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,esk4_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_9])])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_46]), c_0_9])])).
% 0.19/0.40  cnf(c_0_65, plain, (~r2_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_59])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63]), c_0_64])])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (~r2_orders_2(esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_15]), c_0_10])])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_46, c_0_66])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk3_0,X1)|~v6_orders_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_66]), c_0_66]), c_0_66])]), c_0_67]), c_0_68])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_66]), c_0_66])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (v6_orders_2(esk1_3(esk2_0,esk3_0,esk3_0),esk2_0)), inference(rw,[status(thm)],[c_0_63, c_0_66])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_64, c_0_66])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 74
% 0.19/0.40  # Proof object clause steps            : 65
% 0.19/0.40  # Proof object formula steps           : 9
% 0.19/0.40  # Proof object conjectures             : 54
% 0.19/0.40  # Proof object clause conjectures      : 51
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 24
% 0.19/0.40  # Proof object initial formulas used   : 4
% 0.19/0.40  # Proof object generating inferences   : 35
% 0.19/0.40  # Proof object simplifying inferences  : 91
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 4
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 28
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 28
% 0.19/0.40  # Processed clauses                    : 133
% 0.19/0.40  # ...of these trivial                  : 17
% 0.19/0.40  # ...subsumed                          : 15
% 0.19/0.40  # ...remaining for further processing  : 101
% 0.19/0.40  # Other redundant clauses eliminated   : 1
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 11
% 0.19/0.40  # Backward-rewritten                   : 54
% 0.19/0.40  # Generated clauses                    : 116
% 0.19/0.40  # ...of the previous two non-trivial   : 145
% 0.19/0.40  # Contextual simplify-reflections      : 7
% 0.19/0.40  # Paramodulations                      : 115
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 1
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 35
% 0.19/0.40  #    Positive orientable unit clauses  : 9
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 25
% 0.19/0.40  # Current number of unprocessed clauses: 13
% 0.19/0.40  # ...number of literals in the above   : 44
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 65
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 530
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 117
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 28
% 0.19/0.40  # Unit Clause-clause subsumption calls : 52
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 5
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 137
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 6417
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.066 s
% 0.19/0.40  # System time              : 0.002 s
% 0.19/0.40  # Total time               : 0.068 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
