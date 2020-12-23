%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t41_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:14 EDT 2019

% Result     : Theorem 12.99s
% Output     : CNFRefutation 12.99s
% Verified   : 
% Statistics : Number of formulae       :  229 (18082 expanded)
%              Number of clauses        :  187 (7183 expanded)
%              Number of leaves         :   21 (4686 expanded)
%              Depth                    :   91
%              Number of atoms          : 1273 (157249 expanded)
%              Number of equality atoms :   97 (5593 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   25 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t2_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_o_0_0_xboole_0)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_k9_subset_1)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',idempotence_k9_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',symmetry_r1_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',d7_xboole_0)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',d3_tsep_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t16_xboole_1)).

fof(d5_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_pre_topc(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( X4 = k2_tsep_1(X1,X2,X3)
                    <=> u1_struct_0(X4) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',d5_tsep_1)).

fof(dt_k2_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
        & v1_pre_topc(k2_tsep_1(X1,X2,X3))
        & m1_pre_topc(k2_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_k2_tsep_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',redefinition_k9_subset_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',commutativity_k3_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',idempotence_k3_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',dt_m1_pre_topc)).

fof(t41_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ( ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
                       => ( ~ r1_tsep_1(X2,X4)
                          & ~ r1_tsep_1(X3,X4) ) )
                      & ( ~ r1_tsep_1(X4,k2_tsep_1(X1,X2,X3))
                       => ( ~ r1_tsep_1(X4,X2)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',t41_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t41_tmap_1.p',symmetry_r1_tsep_1)).

fof(c_0_21,plain,(
    ! [X73,X74,X75] :
      ( ~ r2_hidden(X73,X74)
      | ~ m1_subset_1(X74,k1_zfmisc_1(X75))
      | ~ v1_xboole_0(X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_22,plain,(
    ! [X41] : m1_subset_1(esk8_1(X41),X41) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X66,X67] :
      ( ~ m1_subset_1(X66,X67)
      | v1_xboole_0(X67)
      | r2_hidden(X66,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk8_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X76] :
      ( ~ v1_xboole_0(X76)
      | X76 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_29,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,esk8_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( v1_xboole_0(esk8_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_32,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_33,plain,
    ( esk8_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

fof(c_0_35,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X30))
      | m1_subset_1(k9_subset_1(X30,X31,X32),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_36,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X48))
      | k9_subset_1(X48,X49,X49) = X49 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_33])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_39,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,k9_subset_1(X1,X4,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_39])).

cnf(c_0_43,plain,
    ( k9_subset_1(k1_xboole_0,X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_38])])).

fof(c_0_45,plain,(
    ! [X56,X57] :
      ( ~ r1_xboole_0(X56,X57)
      | r1_xboole_0(X57,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_46,plain,(
    ! [X23,X24] :
      ( ( ~ r1_xboole_0(X23,X24)
        | k3_xboole_0(X23,X24) = k1_xboole_0 )
      & ( k3_xboole_0(X23,X24) != k1_xboole_0
        | r1_xboole_0(X23,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_50,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tsep_1(X17,X18)
        | r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) )
      & ( ~ r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | r1_tsep_1(X17,X18)
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_54,plain,(
    ! [X58,X59,X60] : k3_xboole_0(k3_xboole_0(X58,X59),X60) = k3_xboole_0(X58,k3_xboole_0(X59,X60)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_55,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X22 != k2_tsep_1(X19,X20,X21)
        | u1_struct_0(X22) = k3_xboole_0(u1_struct_0(X20),u1_struct_0(X21))
        | v2_struct_0(X22)
        | ~ v1_pre_topc(X22)
        | ~ m1_pre_topc(X22,X19)
        | r1_tsep_1(X20,X21)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19) )
      & ( u1_struct_0(X22) != k3_xboole_0(u1_struct_0(X20),u1_struct_0(X21))
        | X22 = k2_tsep_1(X19,X20,X21)
        | v2_struct_0(X22)
        | ~ v1_pre_topc(X22)
        | ~ m1_pre_topc(X22,X19)
        | r1_tsep_1(X20,X21)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

fof(c_0_56,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v2_struct_0(k2_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( v1_pre_topc(k2_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( m1_pre_topc(k2_tsep_1(X27,X28,X29),X27)
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_57,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(X51))
      | k9_subset_1(X51,X52,X53) = k3_xboole_0(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_58,plain,(
    ! [X65] : k3_xboole_0(X65,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_59,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_60,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_51])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( u1_struct_0(X1) = k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( r1_tsep_1(X1,X2)
    | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_49])).

cnf(c_0_73,plain,
    ( k9_subset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_39])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k1_xboole_0
    | k3_xboole_0(X2,k3_xboole_0(X3,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_64])).

cnf(c_0_76,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_65]),c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_77,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_69])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( r1_tsep_1(X1,X2)
    | k3_xboole_0(u1_struct_0(X2),u1_struct_0(X1)) != k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_73])).

cnf(c_0_81,plain,
    ( k3_xboole_0(u1_struct_0(X1),k3_xboole_0(X2,u1_struct_0(X3))) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ r1_tsep_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_70])])).

cnf(c_0_82,plain,
    ( u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)) = k3_xboole_0(u1_struct_0(X3),k3_xboole_0(u1_struct_0(X4),u1_struct_0(X5)))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_76]),c_0_63]),c_0_68])).

cnf(c_0_83,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

fof(c_0_84,plain,(
    ! [X47] : k3_xboole_0(X47,X47) = X47 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_85,plain,
    ( r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,plain,
    ( u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_24])).

fof(c_0_88,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | l1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_89,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_pre_topc(X35,X34)
      | l1_pre_topc(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_90,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
    ( r1_tsep_1(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5),X6)
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | ~ l1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5))
    | ~ l1_struct_0(X6)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])])).

cnf(c_0_92,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_93,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_94,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X2)) = u1_struct_0(X2)
    | r1_tsep_1(X2,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_76])).

cnf(c_0_95,plain,
    ( r1_tsep_1(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5),X6)
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X6)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( l1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_66])).

fof(c_0_97,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( ~ r1_tsep_1(X2,X3)
                     => ( ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
                         => ( ~ r1_tsep_1(X2,X4)
                            & ~ r1_tsep_1(X3,X4) ) )
                        & ( ~ r1_tsep_1(X4,k2_tsep_1(X1,X2,X3))
                         => ( ~ r1_tsep_1(X4,X2)
                            & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_tmap_1])).

cnf(c_0_98,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | r1_tsep_1(X2,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_struct_0(k2_tsep_1(X3,X2,X2))
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,k2_tsep_1(X3,X2,X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_94])).

cnf(c_0_99,plain,
    ( r1_tsep_1(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5),X6)
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | ~ l1_struct_0(X6)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_68])).

fof(c_0_100,plain,(
    ! [X54,X55] :
      ( ~ l1_struct_0(X54)
      | ~ l1_struct_0(X55)
      | ~ r1_tsep_1(X54,X55)
      | r1_tsep_1(X55,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_101,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ r1_tsep_1(esk2_0,esk3_0)
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_97])])])])])).

cnf(c_0_102,plain,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)),u1_struct_0(X6))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | r1_tsep_1(X6,X6)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | ~ l1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5))
    | ~ l1_struct_0(k2_tsep_1(X7,X6,X6))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X6,X7)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_107,plain,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)),u1_struct_0(X6))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X6,X6)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X6)
    | v2_struct_0(X7)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | ~ l1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X6,X7)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(k2_tsep_1(X7,X6,X6))
    | ~ l1_pre_topc(X7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_102,c_0_92])).

cnf(c_0_108,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_105]),c_0_106])])).

cnf(c_0_110,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_111,plain,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)),u1_struct_0(X6))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | r1_tsep_1(X6,X6)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | ~ l1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X6,X7)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_107,c_0_96])).

cnf(c_0_112,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_92]),c_0_109])])).

cnf(c_0_113,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_110]),c_0_106])])).

cnf(c_0_114,plain,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)),u1_struct_0(k2_tsep_1(X6,X7,X8)))
    | r1_tsep_1(k2_tsep_1(X6,X7,X8),k2_tsep_1(X6,X7,X8))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X8)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | ~ l1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X8,X6)
    | ~ m1_pre_topc(X7,X6)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_66]),c_0_68])).

cnf(c_0_115,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_92]),c_0_113])])).

cnf(c_0_116,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_117,plain,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)),u1_struct_0(k2_tsep_1(X6,X7,X8)))
    | r1_tsep_1(k2_tsep_1(X6,X7,X8),k2_tsep_1(X6,X7,X8))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | v2_struct_0(X7)
    | v2_struct_0(X8)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X8,X6)
    | ~ m1_pre_topc(X7,X6)
    | ~ l1_pre_topc(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5))
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_114,c_0_92])).

cnf(c_0_118,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_116]),c_0_106])])).

cnf(c_0_120,plain,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X2,X3,X4),X5)),u1_struct_0(k2_tsep_1(X6,X7,X8)))
    | r1_tsep_1(k2_tsep_1(X6,X7,X8),k2_tsep_1(X6,X7,X8))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),X5)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X8)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ r1_tsep_1(X5,X3)
    | ~ m1_pre_topc(k2_tsep_1(X2,X3,X4),X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X8,X6)
    | ~ m1_pre_topc(X7,X6)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_96]),c_0_68])).

cnf(c_0_121,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_92]),c_0_119])])).

cnf(c_0_122,plain,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(X1,k2_tsep_1(X1,X2,X3),X4)),u1_struct_0(k2_tsep_1(X5,X6,X7)))
    | r1_tsep_1(k2_tsep_1(X5,X6,X7),k2_tsep_1(X5,X6,X7))
    | r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X6)
    | v2_struct_0(X7)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X4)
    | ~ r1_tsep_1(X4,X2)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X7,X5)
    | ~ m1_pre_topc(X6,X5)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_66])).

cnf(c_0_123,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_124,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_125,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_92]),c_0_113])])).

cnf(c_0_126,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,X2),esk3_0)),u1_struct_0(k2_tsep_1(X3,X4,X5)))
    | r1_tsep_1(k2_tsep_1(X3,X4,X5),k2_tsep_1(X3,X4,X5))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),esk3_0)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_105]),c_0_106])]),c_0_123]),c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,X2),esk3_0)),u1_struct_0(k2_tsep_1(X3,X4,X5)))
    | r1_tsep_1(k2_tsep_1(X3,X4,X5),k2_tsep_1(X3,X4,X5))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),esk3_0)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_92]),c_0_109])])).

cnf(c_0_129,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_130,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_92]),c_0_109])])).

cnf(c_0_131,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,esk2_0),esk3_0)),u1_struct_0(k2_tsep_1(X2,X3,X4)))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),k2_tsep_1(X2,X3,X4))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,esk2_0),esk3_0)
    | r1_tsep_1(X1,esk2_0)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_116]),c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_133,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_92]),c_0_113])])).

cnf(c_0_134,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)),u1_struct_0(k2_tsep_1(X1,X2,X3)))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X3))
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_110]),c_0_132]),c_0_133])).

cnf(c_0_135,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)),u1_struct_0(k2_tsep_1(X1,X2,X3)))
    | r1_tsep_1(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X3))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_92]),c_0_113])])).

cnf(c_0_136,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)),u1_struct_0(k2_tsep_1(esk1_0,X1,esk4_0)))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,esk4_0),k2_tsep_1(esk1_0,X1,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_110]),c_0_106])]),c_0_132]),c_0_124])).

cnf(c_0_137,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)),u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_110]),c_0_132])).

cnf(c_0_138,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)),u1_struct_0(esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_94]),c_0_110]),c_0_106])]),c_0_124]),c_0_132])).

cnf(c_0_139,plain,
    ( k3_xboole_0(u1_struct_0(X1),k3_xboole_0(u1_struct_0(X2),k3_xboole_0(X3,u1_struct_0(X4)))) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(X5,X4,X1),X2)
    | r1_tsep_1(X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | k3_xboole_0(X3,u1_struct_0(k2_tsep_1(X6,k2_tsep_1(X5,X4,X1),X2))) != k1_xboole_0
    | ~ m1_pre_topc(k2_tsep_1(X5,X4,X1),X6)
    | ~ m1_pre_topc(X2,X6)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_82]),c_0_63])).

cnf(c_0_140,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0))) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_138]),c_0_71])).

cnf(c_0_141,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_71]),c_0_63])).

cnf(c_0_142,plain,
    ( r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k3_xboole_0(u1_struct_0(X4),k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))) != k1_xboole_0
    | ~ l1_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_struct_0(X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_76])).

cnf(c_0_143,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_90]),c_0_71]),c_0_141]),c_0_105]),c_0_116]),c_0_110]),c_0_106])]),c_0_123]),c_0_124]),c_0_129]),c_0_132])).

cnf(c_0_144,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_145,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_144]),c_0_129]),c_0_123])).

cnf(c_0_146,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_145,c_0_92])).

cnf(c_0_147,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk1_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_96]),c_0_123]),c_0_129])).

cnf(c_0_148,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_66]),c_0_116]),c_0_110]),c_0_106])]),c_0_124]),c_0_132]),c_0_129])).

cnf(c_0_149,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_92]),c_0_113])])).

cnf(c_0_150,plain,
    ( u1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_75])).

cnf(c_0_151,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_105]),c_0_116]),c_0_106])]),c_0_124])).

cnf(c_0_152,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_153,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(k2_tsep_1(X3,X1,X2)) != k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_76])).

cnf(c_0_154,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_152,c_0_92])).

cnf(c_0_155,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_110]),c_0_106])]),c_0_124]),c_0_132])).

cnf(c_0_156,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_157,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_96]),c_0_110]),c_0_106])]),c_0_132]),c_0_124])).

cnf(c_0_158,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_157])).

cnf(c_0_159,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k1_xboole_0
    | k3_xboole_0(X2,k3_xboole_0(X1,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_71])).

cnf(c_0_160,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_157]),c_0_158])).

cnf(c_0_161,plain,
    ( k3_xboole_0(u1_struct_0(X1),k3_xboole_0(X2,u1_struct_0(X3))) = k1_xboole_0
    | r1_tsep_1(X1,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | k3_xboole_0(X2,u1_struct_0(k2_tsep_1(X4,X1,X3))) != k1_xboole_0
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ l1_pre_topc(X4) ),
    inference(spm,[status(thm)],[c_0_159,c_0_76])).

cnf(c_0_162,plain,
    ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_75])).

cnf(c_0_163,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_92])).

cnf(c_0_164,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_90])).

cnf(c_0_165,plain,
    ( k3_xboole_0(u1_struct_0(X1),k3_xboole_0(u1_struct_0(X2),X3)) = k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_75]),c_0_78])).

cnf(c_0_166,plain,
    ( k3_xboole_0(u1_struct_0(X1),k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))) = k1_xboole_0
    | r1_tsep_1(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_struct_0(k2_tsep_1(X4,X1,X3))
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(k2_tsep_1(X4,X1,X3),X2)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ l1_pre_topc(X4) ),
    inference(spm,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_167,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk2_0),esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_96]),c_0_105]),c_0_116]),c_0_106])]),c_0_123]),c_0_129]),c_0_124])).

cnf(c_0_168,plain,
    ( k3_xboole_0(u1_struct_0(X1),X2) = k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_169,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) = k1_xboole_0
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_71]),c_0_116]),c_0_110]),c_0_106])]),c_0_129]),c_0_132]),c_0_124]),c_0_168])).

cnf(c_0_170,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ l1_struct_0(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_169]),c_0_144]),c_0_129]),c_0_123])).

cnf(c_0_171,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_170,c_0_92])).

cnf(c_0_172,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk2_0))
    | ~ l1_pre_topc(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_171,c_0_92])).

cnf(c_0_173,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_96]),c_0_116]),c_0_110]),c_0_106])]),c_0_129]),c_0_132]),c_0_124])).

cnf(c_0_174,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_96]),c_0_123]),c_0_129])).

cnf(c_0_175,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(X1,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_174])).

cnf(c_0_176,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(X1,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_175,c_0_92])).

cnf(c_0_177,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,X2),esk4_0)),u1_struct_0(k2_tsep_1(X3,X4,X5)))
    | r1_tsep_1(k2_tsep_1(X3,X4,X5),k2_tsep_1(X3,X4,X5))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),esk4_0)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_110]),c_0_106])]),c_0_132]),c_0_124])).

cnf(c_0_178,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_174]),c_0_105]),c_0_116]),c_0_106])]),c_0_124])).

cnf(c_0_179,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(X1,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_96]),c_0_123]),c_0_129])).

cnf(c_0_180,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,X2),esk4_0)),u1_struct_0(k2_tsep_1(X3,X4,X5)))
    | r1_tsep_1(k2_tsep_1(X3,X4,X5),k2_tsep_1(X3,X4,X5))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,X2),esk4_0)
    | r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_92]),c_0_113])])).

cnf(c_0_181,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_179]),c_0_105]),c_0_116]),c_0_106])]),c_0_124])).

cnf(c_0_182,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)),u1_struct_0(k2_tsep_1(X2,X3,X4)))
    | r1_tsep_1(k2_tsep_1(X2,X3,X4),k2_tsep_1(X2,X3,X4))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,esk3_0),esk4_0)
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_105]),c_0_123])).

cnf(c_0_183,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_92]),c_0_109])])).

cnf(c_0_184,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)),u1_struct_0(k2_tsep_1(X1,X2,X3)))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_struct_0(esk2_0)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_116]),c_0_144]),c_0_129])).

cnf(c_0_185,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_92]),c_0_113])])).

cnf(c_0_186,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)),u1_struct_0(k2_tsep_1(X1,X2,X3)))
    | r1_tsep_1(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X3))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_184,c_0_185])])).

cnf(c_0_187,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)),u1_struct_0(k2_tsep_1(X1,X2,X3)))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(X1,X2,X3),k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_92]),c_0_119])])).

cnf(c_0_188,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)),u1_struct_0(k2_tsep_1(esk1_0,X1,esk4_0)))
    | r1_tsep_1(k2_tsep_1(esk1_0,X1,esk4_0),k2_tsep_1(esk1_0,X1,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_110]),c_0_106])]),c_0_124]),c_0_132])).

cnf(c_0_189,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_190,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)),u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_110]),c_0_132])).

cnf(c_0_191,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4))) = k1_xboole_0
    | k3_xboole_0(X2,k3_xboole_0(X4,k3_xboole_0(X1,X3))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_159,c_0_189])).

cnf(c_0_192,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)),u1_struct_0(esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_94]),c_0_110]),c_0_106])]),c_0_124]),c_0_132])).

cnf(c_0_193,plain,
    ( k3_xboole_0(u1_struct_0(X1),k3_xboole_0(X2,k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4)))) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(X5,X4,X1),X3)
    | r1_tsep_1(X4,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | k3_xboole_0(X2,u1_struct_0(k2_tsep_1(X6,k2_tsep_1(X5,X4,X1),X3))) != k1_xboole_0
    | ~ m1_pre_topc(k2_tsep_1(X5,X4,X1),X6)
    | ~ m1_pre_topc(X3,X6)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X5) ),
    inference(spm,[status(thm)],[c_0_191,c_0_82])).

cnf(c_0_194,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),u1_struct_0(k2_tsep_1(esk1_0,k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_192]),c_0_71])).

cnf(c_0_195,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk4_0),k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_193,c_0_194]),c_0_164]),c_0_189]),c_0_71]),c_0_141]),c_0_110]),c_0_105]),c_0_116]),c_0_106])]),c_0_144]),c_0_132]),c_0_124]),c_0_123]),c_0_129])).

cnf(c_0_196,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_195]),c_0_144]),c_0_129]),c_0_123])).

cnf(c_0_197,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(k2_tsep_1(X1,esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_196,c_0_92])).

cnf(c_0_198,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_96]),c_0_123]),c_0_129])).

cnf(c_0_199,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_66]),c_0_105]),c_0_116]),c_0_106])]),c_0_124]),c_0_129]),c_0_123])).

cnf(c_0_200,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(k2_tsep_1(X1,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_92]),c_0_113])])).

cnf(c_0_201,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk4_0,esk4_0),k2_tsep_1(esk1_0,esk4_0,esk4_0))
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_105]),c_0_116]),c_0_106])]),c_0_124])).

cnf(c_0_202,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_150,c_0_201])).

cnf(c_0_203,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(esk1_0,esk4_0,esk4_0)) = k1_xboole_0
    | r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_202,c_0_92])).

cnf(c_0_204,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_203]),c_0_110]),c_0_106])]),c_0_124]),c_0_132])).

cnf(c_0_205,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_96]),c_0_110]),c_0_106])]),c_0_132]),c_0_124])).

cnf(c_0_206,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_205])).

cnf(c_0_207,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_205]),c_0_206])).

cnf(c_0_208,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k1_xboole_0
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_90])).

cnf(c_0_209,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_164])).

cnf(c_0_210,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_207,c_0_92])).

cnf(c_0_211,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k1_xboole_0
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_208]),c_0_78]),c_0_63]),c_0_209])).

cnf(c_0_212,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_96]),c_0_105]),c_0_116]),c_0_106])]),c_0_123]),c_0_129]),c_0_124])).

cnf(c_0_213,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_211]),c_0_90])).

cnf(c_0_214,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_212,c_0_92]),c_0_113])])).

cnf(c_0_215,plain,
    ( r1_tsep_1(X1,X2)
    | u1_struct_0(X2) != k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_213])).

cnf(c_0_216,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_214])).

cnf(c_0_217,plain,
    ( r1_tsep_1(X1,X2)
    | u1_struct_0(X2) != k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_215,c_0_92])).

cnf(c_0_218,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_92]),c_0_113])])).

cnf(c_0_219,plain,
    ( r1_tsep_1(X1,X2)
    | u1_struct_0(X1) != k1_xboole_0
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_213])).

cnf(c_0_220,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_217,c_0_218]),c_0_113])])).

cnf(c_0_221,plain,
    ( r1_tsep_1(X1,X2)
    | u1_struct_0(X1) != k1_xboole_0
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_219,c_0_92])).

cnf(c_0_222,negated_conjecture,
    ( r1_tsep_1(X1,esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_220,c_0_92])).

cnf(c_0_223,plain,
    ( r1_tsep_1(X1,X2)
    | u1_struct_0(X1) != k1_xboole_0
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_221,c_0_92])).

cnf(c_0_224,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(X1,X2,X3),esk4_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_222,c_0_96])).

cnf(c_0_225,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223,c_0_218]),c_0_113])])).

cnf(c_0_226,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_224]),c_0_105]),c_0_116]),c_0_106])]),c_0_124]),c_0_129]),c_0_123])).

cnf(c_0_227,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_225,c_0_96])).

cnf(c_0_228,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226,c_0_227]),c_0_105]),c_0_116]),c_0_106])]),c_0_124]),c_0_129]),c_0_123]),
    [proof]).
%------------------------------------------------------------------------------
