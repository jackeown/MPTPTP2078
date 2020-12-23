%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1587+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:27 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 121 expanded)
%              Number of clauses        :   23 (  40 expanded)
%              Number of leaves         :    4 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 ( 987 expanded)
%              Number of equality atoms :    9 (  77 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ( ( r2_yellow_0(X1,k7_domain_1(u1_struct_0(X2),X3,X4))
                      & r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X2),X3,X4)),u1_struct_0(X2)) )
                   => ( r2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))
                      & k2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4)) = k2_yellow_0(X1,k7_domain_1(u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_yellow_0)).

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t64_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r2_yellow_0(X1,X3)
                  & r2_hidden(k2_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r2_yellow_0(X2,X3)
                  & k2_yellow_0(X2,X3) = k2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ( ( r2_yellow_0(X1,k7_domain_1(u1_struct_0(X2),X3,X4))
                        & r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X2),X3,X4)),u1_struct_0(X2)) )
                     => ( r2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))
                        & k2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4)) = k2_yellow_0(X1,k7_domain_1(u1_struct_0(X2),X3,X4)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t66_yellow_0])).

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( v1_xboole_0(X5)
      | ~ m1_subset_1(X6,X5)
      | ~ m1_subset_1(X7,X5)
      | m1_subset_1(k7_domain_1(X5,X6,X7),k1_zfmisc_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v4_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & r2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0))
    & r2_hidden(k2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),u1_struct_0(esk2_0))
    & ( ~ r2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0))
      | k2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) != k2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] :
      ( ( r2_yellow_0(X9,X10)
        | ~ r2_yellow_0(X8,X10)
        | ~ r2_hidden(k2_yellow_0(X8,X10),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v4_yellow_0(X9,X8)
        | ~ m1_yellow_0(X9,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( k2_yellow_0(X9,X10) = k2_yellow_0(X8,X10)
        | ~ r2_yellow_0(X8,X10)
        | ~ r2_hidden(k2_yellow_0(X8,X10),u1_struct_0(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v4_yellow_0(X9,X8)
        | ~ m1_yellow_0(X9,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_yellow_0])])])])])).

cnf(c_0_9,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_yellow_0(X3,X2)
    | ~ r2_hidden(k2_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k7_domain_1(u1_struct_0(esk2_0),X1,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( r2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_12]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_yellow_0(X3,X2)
    | ~ r2_hidden(k2_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0))
    | k2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) != k2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( r2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( k2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) = k2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0))
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_12]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k2_yellow_0(esk1_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) != k2_yellow_0(esk2_0,k7_domain_1(u1_struct_0(esk2_0),esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_25])]),c_0_30]),
    [proof]).

%------------------------------------------------------------------------------
