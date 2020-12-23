%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1145+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  58 expanded)
%              Number of clauses        :   18 (  21 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 265 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_orders_2,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v6_orders_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,X2)
               => ( v6_orders_2(X3,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t96_orders_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r7_relat_2(X3,X1)
          & r1_tarski(X2,X1) )
       => r7_relat_2(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_orders_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => ( v6_orders_2(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t37_orders_2])).

fof(c_0_6,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | m1_subset_1(u1_orders_2(X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X9)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & v6_orders_2(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & r1_tarski(esk3_0,esk2_0)
    & ( ~ v6_orders_2(esk3_0,esk1_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r7_relat_2(X12,X10)
      | ~ r1_tarski(X11,X10)
      | r7_relat_2(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t96_orders_1])])).

fof(c_0_9,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_10,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r7_relat_2(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r7_relat_2(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r7_relat_2(X1,esk3_0)
    | ~ r7_relat_2(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ( ~ v6_orders_2(X8,X7)
        | r7_relat_2(u1_orders_2(X7),X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) )
      & ( ~ r7_relat_2(u1_orders_2(X7),X8)
        | v6_orders_2(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_19,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk1_0),esk3_0)
    | ~ r7_relat_2(u1_orders_2(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r7_relat_2(u1_orders_2(X2),X1)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v6_orders_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( ~ v6_orders_2(esk3_0,esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_11]),c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( ~ v6_orders_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_11]),c_0_24])]),c_0_27]),
    [proof]).

%------------------------------------------------------------------------------
