%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t159_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:17 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 959 expanded)
%              Number of clauses        :   63 ( 390 expanded)
%              Number of leaves         :   16 ( 242 expanded)
%              Depth                    :   17
%              Number of atoms          :  378 (5159 expanded)
%              Number of equality atoms :   26 ( 167 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_orders_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_2(X2)
        & v4_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k3_relat_1(X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',t100_orders_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',dt_u1_orders_2)).

fof(fc2_orders_2,axiom,(
    ! [X1] :
      ( ( v2_orders_2(X1)
        & l1_orders_2(X1) )
     => v1_partfun1(u1_orders_2(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',fc2_orders_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',cc1_relset_1)).

fof(fc5_orders_2,axiom,(
    ! [X1] :
      ( ( v2_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => v8_relat_2(u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',fc5_orders_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',d9_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',d11_orders_1)).

fof(fc4_orders_2,axiom,(
    ! [X1] :
      ( ( v2_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => v4_relat_2(u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',fc4_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',t159_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',d10_orders_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',t1_subset)).

fof(fc3_orders_2,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => v1_relat_2(u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',fc3_orders_2)).

fof(cc1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
       => v2_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',cc1_orders_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t159_orders_2.p',t2_subset)).

fof(c_0_16,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_2(X49)
      | ~ v4_relat_2(X49)
      | ~ v8_relat_2(X49)
      | ~ v1_partfun1(X49,X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X48)))
      | k3_relat_1(X49) = X48 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_orders_1])])).

fof(c_0_17,plain,(
    ! [X29] :
      ( ~ l1_orders_2(X29)
      | m1_subset_1(u1_orders_2(X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X29)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_18,plain,
    ( k3_relat_1(X1) = X2
    | ~ v1_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X72] :
      ( ~ v2_orders_2(X72)
      | ~ l1_orders_2(X72)
      | v1_partfun1(u1_orders_2(X72),u1_struct_0(X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_orders_2])])).

fof(c_0_21,plain,(
    ! [X69,X70,X71] :
      ( ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | v1_relat_1(X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,plain,
    ( k3_relat_1(u1_orders_2(X1)) = u1_struct_0(X1)
    | ~ v1_partfun1(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v8_relat_2(u1_orders_2(X1))
    | ~ v4_relat_2(u1_orders_2(X1))
    | ~ v1_relat_2(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( v1_partfun1(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v2_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X76] :
      ( ~ v2_orders_2(X76)
      | ~ v4_orders_2(X76)
      | ~ l1_orders_2(X76)
      | v8_relat_2(u1_orders_2(X76)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_orders_2])])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r1_orders_2(X21,X22,X23)
        | r2_hidden(k4_tarski(X22,X23),u1_orders_2(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( ~ r2_hidden(k4_tarski(X22,X23),u1_orders_2(X21))
        | r1_orders_2(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_26,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r2_hidden(X17,k3_relat_1(X16))
        | ~ r6_orders_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(X18,k3_relat_1(X16))
        | X18 = X17
        | ~ r2_hidden(k4_tarski(X17,X18),X16)
        | ~ r6_orders_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk4_2(X16,X19),k3_relat_1(X16))
        | ~ r2_hidden(X19,k3_relat_1(X16))
        | r6_orders_1(X16,X19)
        | ~ v1_relat_1(X16) )
      & ( esk4_2(X16,X19) != X19
        | ~ r2_hidden(X19,k3_relat_1(X16))
        | r6_orders_1(X16,X19)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(X19,esk4_2(X16,X19)),X16)
        | ~ r2_hidden(X19,k3_relat_1(X16))
        | r6_orders_1(X16,X19)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_1])])])])])])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_relat_1(u1_orders_2(X1)) = u1_struct_0(X1)
    | ~ v2_orders_2(X1)
    | ~ v8_relat_2(u1_orders_2(X1))
    | ~ v4_relat_2(u1_orders_2(X1))
    | ~ v1_relat_2(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( v8_relat_2(u1_orders_2(X1))
    | ~ v2_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X75] :
      ( ~ v2_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ l1_orders_2(X75)
      | v4_relat_2(u1_orders_2(X75)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_orders_2])])).

fof(c_0_31,negated_conjecture,(
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

fof(c_0_32,plain,(
    ! [X73] :
      ( v2_struct_0(X73)
      | ~ l1_struct_0(X73)
      | ~ v1_xboole_0(u1_struct_0(X73)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_33,plain,(
    ! [X28] :
      ( ~ l1_orders_2(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_34,plain,(
    ! [X13,X14,X15] :
      ( ( r1_orders_2(X13,X14,X15)
        | ~ r2_orders_2(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ l1_orders_2(X13) )
      & ( X14 != X15
        | ~ r2_orders_2(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ l1_orders_2(X13) )
      & ( ~ r1_orders_2(X13,X14,X15)
        | X14 = X15
        | r2_orders_2(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_35,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,esk4_2(X2,X1)),X2)
    | r6_orders_1(X2,X1)
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

fof(c_0_38,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | m1_subset_1(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_39,plain,
    ( k3_relat_1(u1_orders_2(X1)) = u1_struct_0(X1)
    | ~ v2_orders_2(X1)
    | ~ v4_relat_2(u1_orders_2(X1))
    | ~ v1_relat_2(u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( v4_relat_2(u1_orders_2(X1))
    | ~ v2_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X74] :
      ( ~ v3_orders_2(X74)
      | ~ l1_orders_2(X74)
      | v1_relat_2(u1_orders_2(X74)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_orders_2])])).

fof(c_0_42,plain,(
    ! [X68] :
      ( ~ l1_orders_2(X68)
      | ~ v3_orders_2(X68)
      | v2_orders_2(X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_orders_2])])).

fof(c_0_43,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X53,X54)
      | v1_xboole_0(X54)
      | r2_hidden(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_44,negated_conjecture,(
    ! [X8] :
      ( ~ v2_struct_0(esk1_0)
      & v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
        | ~ r6_orders_1(u1_orders_2(esk1_0),esk2_0) )
      & ( r2_orders_2(esk1_0,esk2_0,esk3_0)
        | ~ r6_orders_1(u1_orders_2(esk1_0),esk2_0) )
      & ( r6_orders_1(u1_orders_2(esk1_0),esk2_0)
        | ~ m1_subset_1(X8,u1_struct_0(esk1_0))
        | ~ r2_orders_2(esk1_0,esk2_0,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( r1_orders_2(X1,X2,esk4_2(u1_orders_2(X1),X2))
    | r6_orders_1(u1_orders_2(X1),X2)
    | ~ r2_hidden(X2,k3_relat_1(u1_orders_2(X1)))
    | ~ m1_subset_1(esk4_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( r2_hidden(esk4_2(X1,X2),k3_relat_1(X1))
    | r6_orders_1(X1,X2)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,plain,
    ( k3_relat_1(u1_orders_2(X1)) = u1_struct_0(X1)
    | ~ v2_orders_2(X1)
    | ~ v1_relat_2(u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_52,plain,
    ( v1_relat_2(u1_orders_2(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( v2_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk1_0),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_orders_2(esk1_0,esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( esk4_2(u1_orders_2(X1),X2) = X2
    | r2_orders_2(X1,X2,esk4_2(u1_orders_2(X1),X2))
    | r6_orders_1(u1_orders_2(X1),X2)
    | ~ r2_hidden(X2,k3_relat_1(u1_orders_2(X1)))
    | ~ m1_subset_1(esk4_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_61,plain,
    ( r6_orders_1(X1,X2)
    | m1_subset_1(esk4_2(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,plain,
    ( k3_relat_1(u1_orders_2(X1)) = u1_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( esk4_2(u1_orders_2(esk1_0),esk2_0) = esk2_0
    | r6_orders_1(u1_orders_2(esk1_0),esk2_0)
    | ~ r2_hidden(esk2_0,k3_relat_1(u1_orders_2(esk1_0)))
    | ~ m1_subset_1(esk4_2(u1_orders_2(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_55]),c_0_58])])).

cnf(c_0_66,plain,
    ( r6_orders_1(u1_orders_2(X1),X2)
    | m1_subset_1(esk4_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r6_orders_1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_72,plain,
    ( r6_orders_1(X1,X2)
    | esk4_2(X1,X2) != X2
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( esk4_2(u1_orders_2(esk1_0),esk2_0) = esk2_0
    | r6_orders_1(u1_orders_2(esk1_0),esk2_0)
    | ~ r2_hidden(esk2_0,k3_relat_1(u1_orders_2(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_58]),c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_74,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r6_orders_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_75,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r6_orders_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk1_0),esk2_0)
    | ~ v1_relat_1(u1_orders_2(esk1_0))
    | ~ r2_hidden(esk2_0,k3_relat_1(u1_orders_2(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,plain,
    ( X1 = X2
    | ~ r1_orders_2(X3,X2,X1)
    | ~ r2_hidden(X1,k3_relat_1(u1_orders_2(X3)))
    | ~ r6_orders_1(u1_orders_2(X3),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_37])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r6_orders_1(u1_orders_2(X2),X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_62]),c_0_37])).

cnf(c_0_80,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk1_0),esk2_0)
    | ~ v1_relat_1(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_62]),c_0_67]),c_0_58]),c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ r1_orders_2(X3,X2,X1)
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ r6_orders_1(u1_orders_2(X3),X2)
    | ~ l1_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v3_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_62]),c_0_79]),c_0_49])).

cnf(c_0_82,negated_conjecture,
    ( r6_orders_1(u1_orders_2(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_37]),c_0_58])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    | ~ r6_orders_1(u1_orders_2(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_84,negated_conjecture,
    ( X1 = esk2_0
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ r2_hidden(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_58]),c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_85,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r6_orders_1(u1_orders_2(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_82])])).

cnf(c_0_88,negated_conjecture,
    ( X1 = esk2_0
    | ~ r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ r2_orders_2(esk1_0,esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_55]),c_0_58])]),c_0_49])).

cnf(c_0_89,negated_conjecture,
    ( r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_87]),c_0_64])).

cnf(c_0_91,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_92,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])])).

cnf(c_0_93,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r2_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_55]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
