%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1187+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:53 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   96 (4435 expanded)
%              Number of clauses        :   63 (1645 expanded)
%              Number of leaves         :   16 (1096 expanded)
%              Depth                    :   21
%              Number of atoms          :  317 (25253 expanded)
%              Number of equality atoms :   19 ( 270 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r6_orders_1(u1_orders_2(X1),X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ r2_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_orders_2)).

fof(cc1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
       => v2_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(fc5_orders_2,axiom,(
    ! [X1] :
      ( ( v2_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => v8_relat_2(u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_orders_2)).

fof(fc4_orders_2,axiom,(
    ! [X1] :
      ( ( v2_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => v4_relat_2(u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_orders_2)).

fof(fc3_orders_2,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => v1_relat_2(u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_orders_2)).

fof(fc2_orders_2,axiom,(
    ! [X1] :
      ( ( v2_orders_2(X1)
        & l1_orders_2(X1) )
     => v1_partfun1(u1_orders_2(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t100_orders_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_2(X2)
        & v4_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k3_relat_1(X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_orders_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d11_orders_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r6_orders_1(X1,X2)
        <=> ( r2_hidden(X2,k3_relat_1(X1))
            & ! [X3] :
                ~ ( r2_hidden(X3,k3_relat_1(X1))
                  & X3 != X2
                  & r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

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

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r6_orders_1(u1_orders_2(X1),X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ r2_orders_2(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t159_orders_2])).

fof(c_0_17,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_orders_2(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_orders_2])])).

fof(c_0_18,negated_conjecture,(
    ! [X35] :
      ( ~ v2_struct_0(esk2_0)
      & v3_orders_2(esk2_0)
      & v4_orders_2(esk2_0)
      & v5_orders_2(esk2_0)
      & l1_orders_2(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
        | ~ r6_orders_1(u1_orders_2(esk2_0),esk3_0) )
      & ( r2_orders_2(esk2_0,esk3_0,esk4_0)
        | ~ r6_orders_1(u1_orders_2(esk2_0),esk3_0) )
      & ( r6_orders_1(u1_orders_2(esk2_0),esk3_0)
        | ~ m1_subset_1(X35,u1_struct_0(esk2_0))
        | ~ r2_orders_2(esk2_0,esk3_0,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

fof(c_0_19,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | m1_subset_1(u1_orders_2(X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X20)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_20,plain,(
    ! [X25] :
      ( ~ v2_orders_2(X25)
      | ~ v4_orders_2(X25)
      | ~ l1_orders_2(X25)
      | v8_relat_2(u1_orders_2(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_orders_2])])).

cnf(c_0_21,plain,
    ( v2_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X24] :
      ( ~ v2_orders_2(X24)
      | ~ v5_orders_2(X24)
      | ~ l1_orders_2(X24)
      | v4_relat_2(u1_orders_2(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_orders_2])])).

fof(c_0_25,plain,(
    ! [X23] :
      ( ~ v3_orders_2(X23)
      | ~ l1_orders_2(X23)
      | v1_relat_2(u1_orders_2(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_orders_2])])).

fof(c_0_26,plain,(
    ! [X21] :
      ( ~ v2_orders_2(X21)
      | ~ l1_orders_2(X21)
      | v1_partfun1(u1_orders_2(X21),u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_orders_2])])).

fof(c_0_27,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_28,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_2(X27)
      | ~ v4_relat_2(X27)
      | ~ v8_relat_2(X27)
      | ~ v1_partfun1(X27,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26)))
      | k3_relat_1(X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_orders_1])])).

cnf(c_0_29,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( v8_relat_2(u1_orders_2(X1))
    | ~ v2_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( v2_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_33,plain,
    ( v4_relat_2(u1_orders_2(X1))
    | ~ v2_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( v1_relat_2(u1_orders_2(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v1_partfun1(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v2_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_38,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ v1_xboole_0(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_hidden(X12,k3_relat_1(X11))
        | ~ r6_orders_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X13,k3_relat_1(X11))
        | X13 = X12
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | ~ r6_orders_1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk1_2(X11,X14),k3_relat_1(X11))
        | ~ r2_hidden(X14,k3_relat_1(X11))
        | r6_orders_1(X11,X14)
        | ~ v1_relat_1(X11) )
      & ( esk1_2(X11,X14) != X14
        | ~ r2_hidden(X14,k3_relat_1(X11))
        | r6_orders_1(X11,X14)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X14,esk1_2(X11,X14)),X11)
        | ~ r2_hidden(X14,k3_relat_1(X11))
        | r6_orders_1(X11,X14)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_1])])])])])])).

cnf(c_0_41,plain,
    ( k3_relat_1(X1) = X2
    | ~ v1_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( v8_relat_2(u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_22]),c_0_31]),c_0_32])])).

cnf(c_0_44,negated_conjecture,
    ( v4_relat_2(u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_34]),c_0_32])])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_2(u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_23])])).

cnf(c_0_46,negated_conjecture,
    ( v1_partfun1(u1_orders_2(esk2_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_32])])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),k3_relat_1(X1))
    | r6_orders_1(X1,X2)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( k3_relat_1(u1_orders_2(esk2_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

fof(c_0_58,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(u1_orders_2(esk2_0),X1),u1_struct_0(esk2_0))
    | r6_orders_1(u1_orders_2(esk2_0),X1)
    | ~ r2_hidden(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

fof(c_0_61,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_orders_2(X16,X17,X18)
        | r2_hidden(k4_tarski(X17,X18),u1_orders_2(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),u1_orders_2(X16))
        | r1_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(u1_orders_2(esk2_0),esk3_0),u1_struct_0(esk2_0))
    | r6_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk2_0),esk3_0)
    | m1_subset_1(esk1_2(u1_orders_2(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,X1)),X2)
    | r6_orders_1(X2,X1)
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_67,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk2_0),esk3_0)
    | r1_orders_2(esk2_0,X1,esk1_2(u1_orders_2(esk2_0),esk3_0))
    | ~ r2_hidden(k4_tarski(X1,esk1_2(u1_orders_2(esk2_0),esk3_0)),u1_orders_2(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_22])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(u1_orders_2(esk2_0),X1)),u1_orders_2(esk2_0))
    | r6_orders_1(u1_orders_2(esk2_0),X1)
    | ~ r2_hidden(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_53]),c_0_54])])).

fof(c_0_69,plain,(
    ! [X8,X9,X10] :
      ( ( r1_orders_2(X8,X9,X10)
        | ~ r2_orders_2(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( X9 != X10
        | ~ r2_orders_2(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_orders_2(X8) )
      & ( ~ r1_orders_2(X8,X9,X10)
        | X9 = X10
        | r2_orders_2(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_70,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk2_0),esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk1_2(u1_orders_2(esk2_0),esk3_0))
    | ~ r2_hidden(k4_tarski(esk3_0,esk1_2(u1_orders_2(esk2_0),esk3_0)),u1_orders_2(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk1_2(u1_orders_2(esk2_0),esk3_0)),u1_orders_2(esk2_0))
    | r6_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_60])).

cnf(c_0_72,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk2_0),esk3_0)
    | r1_orders_2(esk2_0,esk3_0,esk1_2(u1_orders_2(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk2_0),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_orders_2(esk2_0,esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( esk1_2(u1_orders_2(esk2_0),esk3_0) = esk3_0
    | r6_orders_1(u1_orders_2(esk2_0),esk3_0)
    | r2_orders_2(esk2_0,esk3_0,esk1_2(u1_orders_2(esk2_0),esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_56]),c_0_22])]),c_0_65])).

cnf(c_0_76,plain,
    ( r6_orders_1(X1,X2)
    | esk1_2(X1,X2) != X2
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_77,negated_conjecture,
    ( esk1_2(u1_orders_2(esk2_0),esk3_0) = esk3_0
    | r6_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    | ~ r6_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_53]),c_0_60]),c_0_54])])).

cnf(c_0_80,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r6_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_81,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r6_orders_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_83,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_79])])).

cnf(c_0_85,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X2,X1),u1_orders_2(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ r6_orders_1(u1_orders_2(esk2_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_53]),c_0_54])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_82]),c_0_57])).

cnf(c_0_87,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_88,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_56]),c_0_22])]),c_0_82])])).

cnf(c_0_89,negated_conjecture,
    ( esk4_0 = X1
    | ~ r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk2_0))
    | ~ r6_orders_1(u1_orders_2(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk4_0),u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_82]),c_0_56]),c_0_22])])).

cnf(c_0_91,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_79])])).

cnf(c_0_93,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_56]),c_0_22])]),
    [proof]).

%------------------------------------------------------------------------------
