%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t29_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:38 EDT 2019

% Result     : Theorem 151.20s
% Output     : CNFRefutation 151.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 104 expanded)
%              Number of clauses        :   31 (  40 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 382 expanded)
%              Number of equality atoms :   45 (  45 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_tops_2,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t29_tops_2)).

fof(cc2_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',cc2_pre_topc)).

fof(dt_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k6_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',dt_k6_setfam_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t6_boole)).

fof(fc3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => v1_xboole_0(k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',fc3_struct_0)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',redefinition_k6_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',d1_setfam_1)).

fof(t26_tops_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t26_tops_2)).

fof(t12_tops_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t12_tops_2)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',dt_k7_setfam_1)).

fof(existence_l1_struct_0,axiom,(
    ? [X1] : l1_struct_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',existence_l1_struct_0)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t29_tops_1)).

fof(t16_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t16_tops_2)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v2_tops_2(X2,X1)
             => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tops_2])).

fof(c_0_14,plain,(
    ! [X71,X72] :
      ( ~ v2_pre_topc(X71)
      | ~ l1_pre_topc(X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X71)))
      | ~ v1_xboole_0(X72)
      | v4_pre_topc(X72,X71) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & v2_tops_2(esk2_0,esk1_0)
    & ~ v4_pre_topc(k6_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_16,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v4_pre_topc(X1,esk1_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_21,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27)))
      | m1_subset_1(k6_setfam_1(X27,X28),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_setfam_1])])).

fof(c_0_22,plain,(
    ! [X66] :
      ( ~ v1_xboole_0(X66)
      | X66 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_23,plain,(
    ! [X73] :
      ( ~ l1_struct_0(X73)
      | v1_xboole_0(k1_struct_0(X73)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(k6_setfam_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k6_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(k6_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k1_zfmisc_1(X42)))
      | k6_setfam_1(X42,X43) = k1_setfam_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_28,plain,(
    ! [X9,X10,X11,X12,X13,X15,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X11,X10)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X11,X12)
        | X10 != k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X9,X10,X13),X9)
        | r2_hidden(X13,X10)
        | X10 != k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( ~ r2_hidden(X13,esk3_3(X9,X10,X13))
        | r2_hidden(X13,X10)
        | X10 != k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X9,X15),X9)
        | ~ r2_hidden(esk4_2(X9,X15),X15)
        | X15 = k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X9,X15),esk5_2(X9,X15))
        | ~ r2_hidden(esk4_2(X9,X15),X15)
        | X15 = k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X9,X15),X15)
        | ~ r2_hidden(X18,X9)
        | r2_hidden(esk4_2(X9,X15),X18)
        | X15 = k1_setfam_1(X9)
        | X9 = k1_xboole_0 )
      & ( X20 != k1_setfam_1(X19)
        | X20 = k1_xboole_0
        | X19 != k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | X21 = k1_setfam_1(X19)
        | X19 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X50,X51] :
      ( ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X50))))
      | ~ v1_tops_2(X51,X50)
      | v3_pre_topc(k5_setfam_1(u1_struct_0(X50),X51),X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_tops_2])])])).

fof(c_0_32,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k1_zfmisc_1(X44)))
      | X45 = k1_xboole_0
      | k5_setfam_1(X44,k7_setfam_1(X44,X45)) = k3_subset_1(X44,k6_setfam_1(X44,X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tops_2])])).

fof(c_0_33,plain,(
    ! [X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(X29)))
      | m1_subset_1(k7_setfam_1(X29,X30),k1_zfmisc_1(k1_zfmisc_1(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(k6_setfam_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_35,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    l1_struct_0(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_l1_struct_0])])).

fof(c_0_39,plain,(
    ! [X52,X53] :
      ( ( ~ v4_pre_topc(X53,X52)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X52),X53),X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | ~ l1_pre_topc(X52) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X52),X53),X52)
        | v4_pre_topc(X53,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | ~ l1_pre_topc(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_40,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_tops_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | k5_setfam_1(X2,k7_setfam_1(X2,X1)) = k3_subset_1(X2,k6_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26])])).

cnf(c_0_44,plain,
    ( k1_setfam_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_46,plain,
    ( l1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | v3_pre_topc(k3_subset_1(u1_struct_0(X2),k6_setfam_1(u1_struct_0(X2),X1)),X2)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

fof(c_0_53,plain,(
    ! [X46,X47] :
      ( ( ~ v2_tops_2(X47,X46)
        | v1_tops_2(k7_setfam_1(u1_struct_0(X46),X47),X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X46))))
        | ~ l1_pre_topc(X46) )
      & ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X46),X47),X46)
        | v2_tops_2(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X46))))
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_51]),c_0_26]),c_0_18]),c_0_17])]),c_0_52])).

cnf(c_0_55,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_26]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
