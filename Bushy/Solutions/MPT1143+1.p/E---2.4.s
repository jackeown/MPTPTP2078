%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t35_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:19 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 133 expanded)
%              Number of clauses        :   43 (  57 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  243 ( 514 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d1_tarski)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',t1_subset)).

fof(d7_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r7_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ~ ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & ~ r2_hidden(k4_tarski(X3,X4),X1)
                & ~ r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d7_relat_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',dt_u1_orders_2)).

fof(t35_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
            & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',t35_orders_2)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d11_orders_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',dt_k6_domain_1)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d1_relat_2)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d4_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',redefinition_k6_domain_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',dt_l1_orders_2)).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X16
        | X17 != k1_tarski(X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k1_tarski(X16) )
      & ( ~ r2_hidden(esk4_2(X20,X21),X21)
        | esk4_2(X20,X21) != X20
        | X21 = k1_tarski(X20) )
      & ( r2_hidden(esk4_2(X20,X21),X21)
        | esk4_2(X20,X21) = X20
        | X21 = k1_tarski(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X54,X55] :
      ( ~ r2_hidden(X54,X55)
      | ~ v1_xboole_0(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

fof(c_0_22,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | m1_subset_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_23,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r7_relat_2(X24,X25)
        | ~ r2_hidden(X26,X25)
        | ~ r2_hidden(X27,X25)
        | r2_hidden(k4_tarski(X26,X27),X24)
        | r2_hidden(k4_tarski(X27,X26),X24)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk5_2(X24,X28),X28)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk6_2(X24,X28),X28)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X24,X28),esk6_2(X24,X28)),X24)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk6_2(X24,X28),esk5_2(X24,X28)),X24)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_tarski(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_30,plain,
    ( r7_relat_2(X1,X2)
    | m1_subset_1(esk5_2(X1,X2),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_31,plain,(
    ! [X58,X59,X60] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | v1_relat_1(X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_32,plain,(
    ! [X34] :
      ( ~ l1_orders_2(X34)
      | m1_subset_1(u1_orders_2(X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X34)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
              & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_orders_2])).

fof(c_0_34,plain,(
    ! [X9,X10] :
      ( ( ~ v6_orders_2(X10,X9)
        | r7_relat_2(u1_orders_2(X9),X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( ~ r7_relat_2(u1_orders_2(X9),X10)
        | v6_orders_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

fof(c_0_35,plain,(
    ! [X31,X32] :
      ( v1_xboole_0(X31)
      | ~ m1_subset_1(X32,X31)
      | m1_subset_1(k6_domain_1(X31,X32),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_36,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( esk5_2(X1,k1_tarski(X2)) = X2
    | r7_relat_2(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_39,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r1_relat_2(X11,X12)
        | ~ r2_hidden(X13,X12)
        | r2_hidden(k4_tarski(X13,X13),X11)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_2(X11,X14),X14)
        | r1_relat_2(X11,X14)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X11,X14),esk3_2(X11,X14)),X11)
        | r1_relat_2(X11,X14)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

fof(c_0_40,plain,(
    ! [X23] :
      ( ( ~ v3_orders_2(X23)
        | r1_relat_2(u1_orders_2(X23),u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ r1_relat_2(u1_orders_2(X23),u1_struct_0(X23))
        | v3_orders_2(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).

cnf(c_0_44,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X39,X40] :
      ( v1_xboole_0(X39)
      | ~ m1_subset_1(X40,X39)
      | k6_domain_1(X39,X40) = k1_tarski(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_47,plain,
    ( r7_relat_2(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,esk6_2(X1,k1_tarski(X2))),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( esk6_2(X1,k1_tarski(X2)) = X2
    | r7_relat_2(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_38])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ r7_relat_2(u1_orders_2(X1),k6_domain_1(u1_struct_0(X1),X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( r7_relat_2(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_45]),c_0_53])])).

cnf(c_0_59,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v6_orders_2(k1_tarski(X2),X1)
    | ~ r7_relat_2(u1_orders_2(X1),k1_tarski(X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r7_relat_2(u1_orders_2(X1),k1_tarski(X2))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ v6_orders_2(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_55]),c_0_53])])).

cnf(c_0_62,plain,
    ( v6_orders_2(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_27]),c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_65,plain,(
    ! [X61] :
      ( v2_struct_0(X61)
      | ~ l1_struct_0(X61)
      | ~ v1_xboole_0(u1_struct_0(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])]),c_0_20])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_25]),c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_70,plain,(
    ! [X33] :
      ( ~ l1_orders_2(X33)
      | l1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_71,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_72,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
