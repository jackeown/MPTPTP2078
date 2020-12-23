%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t39_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:49 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 154 expanded)
%              Number of clauses        :   28 (  53 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  225 ( 843 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d18_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k6_waybel_0(X1,X2) = k4_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',d18_waybel_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',redefinition_k6_domain_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',dt_k6_domain_1)).

fof(t39_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_yellow_0(X1,k6_waybel_0(X1,X2))
            & k2_yellow_0(X1,k6_waybel_0(X1,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t39_waybel_0)).

fof(t37_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_yellow_0(X1,X2)
          <=> r2_yellow_0(X1,k4_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t37_waybel_0)).

fof(t38_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_yellow_0(X1,X2)
           => k2_yellow_0(X1,X2) = k2_yellow_0(X1,k4_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t38_waybel_0)).

fof(t38_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))
            & r2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t38_yellow_0)).

fof(t39_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t39_yellow_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',dt_l1_orders_2)).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | k6_waybel_0(X8,X9) = k4_waybel_0(X8,k6_domain_1(u1_struct_0(X8),X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_waybel_0])])])])).

fof(c_0_11,plain,(
    ! [X27,X28] :
      ( v1_xboole_0(X27)
      | ~ m1_subset_1(X28,X27)
      | k6_domain_1(X27,X28) = k1_tarski(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | ~ m1_subset_1(X17,X16)
      | m1_subset_1(k6_domain_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r2_yellow_0(X1,k6_waybel_0(X1,X2))
              & k2_yellow_0(X1,k6_waybel_0(X1,X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_waybel_0])).

fof(c_0_14,plain,(
    ! [X33,X34] :
      ( ( ~ r2_yellow_0(X33,X34)
        | r2_yellow_0(X33,k4_waybel_0(X33,X34))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( ~ r2_yellow_0(X33,k4_waybel_0(X33,X34))
        | r2_yellow_0(X33,X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_waybel_0])])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | k6_waybel_0(X1,X2) = k4_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( ~ r2_yellow_0(esk1_0,k6_waybel_0(esk1_0,esk2_0))
      | k2_yellow_0(esk1_0,k6_waybel_0(esk1_0,esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_19,plain,
    ( r2_yellow_0(X1,k4_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_waybel_0(X1,k1_tarski(X2)) = k6_waybel_0(X1,X2)
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v3_orders_2(X35)
      | ~ v4_orders_2(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ r2_yellow_0(X35,X36)
      | k2_yellow_0(X35,X36) = k2_yellow_0(X35,k4_waybel_0(X35,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_waybel_0])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_yellow_0(esk1_0,k6_waybel_0(esk1_0,esk2_0))
    | k2_yellow_0(esk1_0,k6_waybel_0(esk1_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_yellow_0(X1,k6_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,k1_tarski(X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k2_yellow_0(X1,X2) = k2_yellow_0(X1,k4_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X37,X38] :
      ( ( r1_yellow_0(X37,k6_domain_1(u1_struct_0(X37),X38))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( r2_yellow_0(X37,k6_domain_1(u1_struct_0(X37),X38))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_0])])])])])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | k2_yellow_0(esk1_0,k6_waybel_0(esk1_0,esk2_0)) != esk2_0
    | ~ r2_yellow_0(esk1_0,k1_tarski(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_33,plain,
    ( k2_yellow_0(X1,k6_waybel_0(X1,X2)) = k2_yellow_0(X1,k1_tarski(X2))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,k1_tarski(X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21])).

cnf(c_0_34,plain,
    ( r2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X39,X40] :
      ( ( k1_yellow_0(X39,k6_domain_1(u1_struct_0(X39),X40)) = X40
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39) )
      & ( k2_yellow_0(X39,k6_domain_1(u1_struct_0(X39),X40)) = X40
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | v2_struct_0(X39)
        | ~ v3_orders_2(X39)
        | ~ v5_orders_2(X39)
        | ~ l1_orders_2(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_0])])])])])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | k2_yellow_0(esk1_0,k1_tarski(esk2_0)) != esk2_0
    | ~ r2_yellow_0(esk1_0,k1_tarski(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_37,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_yellow_0(X1,k1_tarski(X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ v1_xboole_0(u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | k2_yellow_0(esk1_0,k1_tarski(esk2_0)) != esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25]),c_0_26]),c_0_38]),c_0_28])]),c_0_29])).

cnf(c_0_42,plain,
    ( k2_yellow_0(X1,k1_tarski(X2)) = X2
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_25]),c_0_26]),c_0_38]),c_0_28])]),c_0_29])).

fof(c_0_45,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_46,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_29])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
