%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1617+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 6.64s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :   25 (  73 expanded)
%              Number of clauses        :   16 (  28 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 267 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_yellow_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_1)).

fof(t78_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT020+2.ax',t78_tops_2)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
            <=> m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_yellow_1])).

fof(c_0_5,plain,(
    ! [X7519,X7520] :
      ( ( ~ v1_tops_2(X7520,X7519)
        | r1_tarski(X7520,u1_pre_topc(X7519))
        | ~ m1_subset_1(X7520,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7519))))
        | ~ l1_pre_topc(X7519) )
      & ( ~ r1_tarski(X7520,u1_pre_topc(X7519))
        | v1_tops_2(X7520,X7519)
        | ~ m1_subset_1(X7520,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7519))))
        | ~ l1_pre_topc(X7519) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).

fof(c_0_6,negated_conjecture,
    ( v2_pre_topc(esk1124_0)
    & l1_pre_topc(esk1124_0)
    & m1_subset_1(esk1125_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1124_0))))
    & ( ~ v1_tops_2(esk1125_0,esk1124_0)
      | ~ m1_subset_1(esk1125_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk1124_0))))) )
    & ( v1_tops_2(esk1125_0,esk1124_0)
      | m1_subset_1(esk1125_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk1124_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X9853] :
      ( u1_struct_0(k2_yellow_1(X9853)) = X9853
      & u1_orders_2(k2_yellow_1(X9853)) = k1_yellow_1(X9853) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk1125_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1124_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk1124_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_tops_2(esk1125_0,esk1124_0)
    | m1_subset_1(esk1125_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk1124_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1125_0,u1_pre_topc(esk1124_0))
    | ~ v1_tops_2(esk1125_0,esk1124_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_15,negated_conjecture,
    ( v1_tops_2(esk1125_0,esk1124_0)
    | m1_subset_1(esk1125_0,k1_zfmisc_1(u1_pre_topc(esk1124_0))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_tops_2(esk1125_0,esk1124_0)
    | ~ m1_subset_1(esk1125_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk1124_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk1125_0,k1_zfmisc_1(u1_pre_topc(esk1124_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_tops_2(esk1125_0,esk1124_0)
    | ~ m1_subset_1(esk1125_0,k1_zfmisc_1(u1_pre_topc(esk1124_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_21,plain,
    ( v1_tops_2(X1,X2)
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk1125_0,u1_pre_topc(esk1124_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_tops_2(esk1125_0,esk1124_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_9]),c_0_10]),c_0_22])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
