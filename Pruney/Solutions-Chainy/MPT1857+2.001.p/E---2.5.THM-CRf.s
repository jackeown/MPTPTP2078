%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   95 (1313 expanded)
%              Number of clauses        :   70 ( 522 expanded)
%              Number of leaves         :   12 ( 312 expanded)
%              Depth                    :   17
%              Number of atoms          :  288 (6415 expanded)
%              Number of equality atoms :   44 (1234 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & X3 = X4
                      & v2_tex_2(X3,X1) )
                   => v2_tex_2(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t33_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v3_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v3_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                        & X3 = X4
                        & v2_tex_2(X3,X1) )
                     => v2_tex_2(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_tex_2])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ( ~ m1_pre_topc(X19,X20)
        | m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
        | m1_pre_topc(X19,X20)
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | m1_pre_topc(X27,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    & esk5_0 = esk6_0
    & v2_tex_2(esk5_0,esk3_0)
    & ~ v2_tex_2(esk6_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | m1_pre_topc(X18,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_22,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

fof(c_0_30,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25])])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_29]),c_0_25])])).

cnf(c_0_39,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25])])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(X1,esk5_0) = k9_subset_1(u1_struct_0(esk4_0),X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_49,plain,(
    ! [X28,X29,X30,X33] :
      ( ( m1_subset_1(esk1_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r1_tarski(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( v3_pre_topc(esk1_3(X28,X29,X30),X28)
        | ~ r1_tarski(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( k9_subset_1(u1_struct_0(X28),X29,esk1_3(X28,X29,X30)) = X30
        | ~ r1_tarski(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk2_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))
        | v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( r1_tarski(esk2_2(X28,X29),X29)
        | v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v3_pre_topc(X33,X28)
        | k9_subset_1(u1_struct_0(X28),X29,X33) != esk2_2(X28,X29)
        | v2_tex_2(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_44]),c_0_20])])).

fof(c_0_54,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | k9_subset_1(X7,X8,X9) = k9_subset_1(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_55,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),X1,esk5_0) = k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_45]),c_0_46])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_61,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk2_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(X1,esk5_0) = k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_55])).

cnf(c_0_64,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_40]),c_0_20])]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_67,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1) != esk2_2(esk4_0,esk5_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_20])]),c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk5_0,X1) = k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0) = k9_subset_1(esk5_0,X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( r1_tarski(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_73,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_pre_topc(X23,X21)
      | ~ v3_pre_topc(X22,X21)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | X24 != X22
      | v3_pre_topc(X24,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).

cnf(c_0_74,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk5_0,X1) != esk2_2(esk4_0,esk5_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_66]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk5_0,X1) = k9_subset_1(esk5_0,X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk2_2(esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_25])])).

cnf(c_0_77,negated_conjecture,
    ( v2_tex_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk2_2(esk4_0,esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_40]),c_0_20])]),c_0_58])).

cnf(c_0_79,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_80,plain,
    ( v3_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k9_subset_1(esk5_0,X1,esk5_0) != esk2_2(esk4_0,esk5_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_45]),c_0_77]),c_0_78])])).

cnf(c_0_83,plain,
    ( k9_subset_1(X1,X1,X2) = k9_subset_1(X1,X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_56])).

cnf(c_0_84,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),X1,esk1_3(esk3_0,X1,esk2_2(esk4_0,esk5_0))) = esk2_2(esk4_0,esk5_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk2_2(esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_71]),c_0_25])])).

cnf(c_0_85,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k9_subset_1(esk5_0,esk5_0,esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0))) != esk2_2(esk4_0,esk5_0)
    | ~ v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k9_subset_1(esk5_0,esk5_0,esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0))) = esk2_2(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_45]),c_0_75]),c_0_83]),c_0_77]),c_0_78])])).

cnf(c_0_88,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_66])).

cnf(c_0_90,negated_conjecture,
    ( ~ v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk3_0,X1,esk2_2(esk4_0,esk5_0)),esk3_0)
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk2_2(esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_71]),c_0_25])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_82]),c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_45]),c_0_77]),c_0_78])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_82]),c_0_93]),c_0_36]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.19/0.40  # and selection function SelectComplexG.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t25_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&X3=X4)&v2_tex_2(X3,X1))=>v2_tex_2(X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tex_2)).
% 0.19/0.40  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.40  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.40  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.19/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.40  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.40  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 0.19/0.40  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.19/0.40  fof(t33_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 0.19/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&X3=X4)&v2_tex_2(X3,X1))=>v2_tex_2(X4,X2))))))), inference(assume_negation,[status(cth)],[t25_tex_2])).
% 0.19/0.40  fof(c_0_13, plain, ![X19, X20]:((~m1_pre_topc(X19,X20)|m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&(~m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|m1_pre_topc(X19,X20)|~l1_pre_topc(X20)|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.40  fof(c_0_14, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.40  fof(c_0_15, plain, ![X27]:(~l1_pre_topc(X27)|m1_pre_topc(X27,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.40  fof(c_0_16, negated_conjecture, (l1_pre_topc(esk3_0)&(l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(((g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))&esk5_0=esk6_0)&v2_tex_2(esk5_0,esk3_0))&~v2_tex_2(esk6_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.40  cnf(c_0_17, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_18, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_19, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_21, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|m1_pre_topc(X18,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.19/0.40  cnf(c_0_22, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_26, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.40  cnf(c_0_27, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_20])])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 0.19/0.40  fof(c_0_30, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (esk5_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_33, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_34, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.40  cnf(c_0_35, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_25])])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_20])])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_29]), c_0_25])])).
% 0.19/0.40  cnf(c_0_39, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.40  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25])])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (k3_xboole_0(X1,esk5_0)=k9_subset_1(u1_struct_0(esk4_0),X1,esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.40  fof(c_0_49, plain, ![X28, X29, X30, X33]:(((m1_subset_1(esk1_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))|~r1_tarski(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&((v3_pre_topc(esk1_3(X28,X29,X30),X28)|~r1_tarski(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(k9_subset_1(u1_struct_0(X28),X29,esk1_3(X28,X29,X30))=X30|~r1_tarski(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|~v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))))&((m1_subset_1(esk2_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))|v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&((r1_tarski(esk2_2(X28,X29),X29)|v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X28)))|(~v3_pre_topc(X33,X28)|k9_subset_1(u1_struct_0(X28),X29,X33)!=esk2_2(X28,X29))|v2_tex_2(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (~v2_tex_2(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_44]), c_0_20])])).
% 0.19/0.40  fof(c_0_54, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X7))|k9_subset_1(X7,X8,X9)=k9_subset_1(X7,X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),X1,esk5_0)=k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_45]), c_0_46])).
% 0.19/0.40  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.40  cnf(c_0_57, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_50, c_0_32])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk3_0)|~r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 0.19/0.40  cnf(c_0_61, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk2_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_62, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (k3_xboole_0(X1,esk5_0)=k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0)), inference(rw,[status(thm)],[c_0_46, c_0_55])).
% 0.19/0.40  cnf(c_0_64, plain, (k9_subset_1(X1,X2,X1)=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_56])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_40]), c_0_20])]), c_0_58])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1)!=esk2_2(esk4_0,esk5_0)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_40]), c_0_20])]), c_0_58])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk5_0,X1)=k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_45])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0)=k9_subset_1(esk5_0,X1,esk5_0)), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.40  cnf(c_0_70, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk2_2(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.40  cnf(c_0_72, plain, (r1_tarski(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  fof(c_0_73, plain, ![X21, X22, X23, X24]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_pre_topc(X23,X21)|(~v3_pre_topc(X22,X21)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(X24!=X22|v3_pre_topc(X24,X23))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk5_0,X1)!=esk2_2(esk4_0,esk5_0)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_66]), c_0_66])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk5_0,X1)=k9_subset_1(esk5_0,X1,esk5_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,X1,esk2_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk2_2(esk4_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_25])])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (v2_tex_2(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (r1_tarski(esk2_2(esk4_0,esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_40]), c_0_20])]), c_0_58])).
% 0.19/0.40  cnf(c_0_79, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_80, plain, (v3_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (k9_subset_1(esk5_0,X1,esk5_0)!=esk2_2(esk4_0,esk5_0)|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_45]), c_0_77]), c_0_78])])).
% 0.19/0.40  cnf(c_0_83, plain, (k9_subset_1(X1,X1,X2)=k9_subset_1(X1,X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_56])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),X1,esk1_3(esk3_0,X1,esk2_2(esk4_0,esk5_0)))=esk2_2(esk4_0,esk5_0)|~v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk2_2(esk4_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_71]), c_0_25])])).
% 0.19/0.40  cnf(c_0_85, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_80])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (k9_subset_1(esk5_0,esk5_0,esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)))!=esk2_2(esk4_0,esk5_0)|~v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (k9_subset_1(esk5_0,esk5_0,esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)))=esk2_2(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_45]), c_0_75]), c_0_83]), c_0_77]), c_0_78])])).
% 0.19/0.40  cnf(c_0_88, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_89, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,X2)|~m1_pre_topc(esk4_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_85, c_0_66])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, (~v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (v3_pre_topc(esk1_3(esk3_0,X1,esk2_2(esk4_0,esk5_0)),esk3_0)|~v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk2_2(esk4_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_71]), c_0_25])])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (~v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_82]), c_0_90])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, (v3_pre_topc(esk1_3(esk3_0,esk5_0,esk2_2(esk4_0,esk5_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_45]), c_0_77]), c_0_78])])).
% 0.19/0.40  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_82]), c_0_93]), c_0_36]), c_0_25])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 95
% 0.19/0.40  # Proof object clause steps            : 70
% 0.19/0.40  # Proof object formula steps           : 25
% 0.19/0.40  # Proof object conjectures             : 49
% 0.19/0.40  # Proof object clause conjectures      : 46
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 26
% 0.19/0.40  # Proof object initial formulas used   : 12
% 0.19/0.40  # Proof object generating inferences   : 31
% 0.19/0.40  # Proof object simplifying inferences  : 62
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 12
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 28
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 28
% 0.19/0.40  # Processed clauses                    : 338
% 0.19/0.40  # ...of these trivial                  : 2
% 0.19/0.40  # ...subsumed                          : 49
% 0.19/0.40  # ...remaining for further processing  : 287
% 0.19/0.40  # Other redundant clauses eliminated   : 3
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 46
% 0.19/0.40  # Generated clauses                    : 664
% 0.19/0.40  # ...of the previous two non-trivial   : 663
% 0.19/0.40  # Contextual simplify-reflections      : 2
% 0.19/0.40  # Paramodulations                      : 661
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 3
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 212
% 0.19/0.40  #    Positive orientable unit clauses  : 34
% 0.19/0.40  #    Positive unorientable unit clauses: 4
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 172
% 0.19/0.40  # Current number of unprocessed clauses: 340
% 0.19/0.40  # ...number of literals in the above   : 1269
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 72
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 4521
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 2677
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 40
% 0.19/0.40  # Unit Clause-clause subsumption calls : 175
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 156
% 0.19/0.40  # BW rewrite match successes           : 48
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 19954
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.061 s
% 0.19/0.41  # System time              : 0.001 s
% 0.19/0.41  # Total time               : 0.062 s
% 0.19/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
