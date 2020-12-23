%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1617+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 363 expanded)
%              Number of clauses        :   59 ( 160 expanded)
%              Number of leaves         :   11 (  91 expanded)
%              Depth                    :   17
%              Number of atoms          :  238 (1221 expanded)
%              Number of equality atoms :   27 ( 147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(t25_yellow_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_1)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25] :
      ( ( X22 = X24
        | g1_orders_2(X22,X23) != g1_orders_2(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22))) )
      & ( X23 = X25
        | g1_orders_2(X22,X23) != g1_orders_2(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_12,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_13,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X20] :
      ( v1_orders_2(k2_yellow_1(X20))
      & l1_orders_2(k2_yellow_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_16,plain,(
    ! [X10] : k2_yellow_1(X10) = g1_orders_2(X10,k1_yellow_1(X10)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
            <=> m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_yellow_1])).

cnf(c_0_18,plain,
    ( X1 = u1_orders_2(X2)
    | g1_orders_2(X3,X1) != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))
    | ~ v1_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X19] :
      ( v1_relat_2(k1_yellow_1(X19))
      & v4_relat_2(k1_yellow_1(X19))
      & v8_relat_2(k1_yellow_1(X19))
      & v1_partfun1(k1_yellow_1(X19),X19)
      & m1_subset_1(k1_yellow_1(X19),k1_zfmisc_1(k2_zfmisc_1(X19,X19))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

cnf(c_0_22,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & ( ~ v1_tops_2(esk4_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))) )
    & ( v1_tops_2(esk4_0,esk3_0)
      | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_24,plain,
    ( u1_orders_2(g1_orders_2(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

fof(c_0_28,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_29,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = k1_yellow_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

fof(c_0_31,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(esk3_0),k1_yellow_1(u1_pre_topc(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_20])).

fof(c_0_34,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_tops_2(X7,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X8,X7)
        | v3_pre_topc(X8,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | v1_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | v1_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( ~ v3_pre_topc(esk1_2(X6,X7),X6)
        | v1_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),k1_yellow_1(X1)) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_30]),c_0_25]),c_0_27])])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(g1_orders_2(u1_pre_topc(esk3_0),k1_yellow_1(u1_pre_topc(esk3_0)))))
    | v1_tops_2(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( X1 = u1_struct_0(g1_orders_2(X2,k1_yellow_1(X2)))
    | g1_orders_2(X1,X3) != g1_orders_2(X2,k1_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(g1_orders_2(u1_pre_topc(esk3_0),k1_yellow_1(u1_pre_topc(esk3_0)))))
    | v1_tops_2(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)
    | v1_tops_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_45,plain,
    ( X1 = u1_struct_0(g1_orders_2(X2,k1_yellow_1(X2)))
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,k1_yellow_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_48,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | m1_subset_1(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_49,plain,(
    ! [X17,X18] :
      ( ( ~ v3_pre_topc(X18,X17)
        | r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(X18,u1_pre_topc(X17))
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),u1_struct_0(g1_orders_2(u1_pre_topc(esk3_0),k1_yellow_1(u1_pre_topc(esk3_0)))))
    | v1_tops_2(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_56,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),u1_pre_topc(esk3_0))
    | v1_tops_2(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0)
    | m1_subset_1(esk1_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_41])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_55])).

cnf(c_0_63,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(esk1_2(esk3_0,esk4_0),esk3_0)
    | v1_tops_2(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_41])]),c_0_60])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | r2_hidden(esk2_2(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ v1_tops_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_40]),c_0_41])])).

cnf(c_0_69,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_40]),c_0_41])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | m1_subset_1(esk2_2(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_tops_2(esk4_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | r2_hidden(esk2_2(esk4_0,X1),u1_pre_topc(esk3_0))
    | ~ v3_pre_topc(esk2_2(esk4_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_41])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | v3_pre_topc(esk2_2(esk4_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_47])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_tops_2(esk4_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(g1_orders_2(u1_pre_topc(esk3_0),k1_yellow_1(u1_pre_topc(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_20])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | r2_hidden(esk2_2(esk4_0,X1),u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_tops_2(esk4_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_pre_topc(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_76,c_0_51])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk4_0,u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_69])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_79]),c_0_80]),
    [proof]).

%------------------------------------------------------------------------------
