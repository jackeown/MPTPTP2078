%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:26 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 172 expanded)
%              Number of clauses        :   36 (  75 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  229 ( 764 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(t46_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | ~ r2_hidden(X15,X14)
      | r2_hidden(X15,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_15,plain,(
    ! [X20] :
      ( ( m1_subset_1(esk2_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v1_xboole_0(esk2_1(X20))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( v4_pre_topc(esk2_1(X20),X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

fof(c_0_16,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X2,esk2_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk2_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X2,esk2_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk1_1(esk2_1(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | k6_domain_1(X24,X25) = k1_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_29,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | v2_tex_2(k6_domain_1(u1_struct_0(X30),X31),X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ~ v3_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t46_tex_2])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ( v2_tex_2(X27,X26)
        | ~ v3_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X28,X26)
        | ~ r1_tarski(X27,X28)
        | X27 = X28
        | ~ v3_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | v3_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( v2_tex_2(esk3_2(X26,X27),X26)
        | ~ v2_tex_2(X27,X26)
        | v3_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( r1_tarski(X27,esk3_2(X26,X27))
        | ~ v2_tex_2(X27,X26)
        | v3_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( X27 != esk3_2(X26,X27)
        | ~ v2_tex_2(X27,X26)
        | v3_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_32,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_33,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_1(esk2_1(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_23])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X11,X12] : k2_xboole_0(k1_tarski(X11),X12) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_39,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_41,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & v3_tex_2(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).

cnf(c_0_43,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_47,plain,
    ( k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(X1))) = k1_tarski(esk1_1(esk2_1(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_35]),c_0_36])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(X1))),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(k1_xboole_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_tarski(esk1_1(esk2_1(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( v2_tex_2(k1_tarski(esk1_1(esk2_1(X1))),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v3_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | ~ v3_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( v3_tex_2(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:23:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.21/0.40  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.039 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.40  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.21/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.40  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.21/0.40  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.21/0.40  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 0.21/0.40  fof(t46_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 0.21/0.40  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.21/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.40  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.21/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.21/0.40  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.21/0.40  fof(c_0_14, plain, ![X13, X14, X15]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|(~r2_hidden(X15,X14)|r2_hidden(X15,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.41  fof(c_0_15, plain, ![X20]:(((m1_subset_1(esk2_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~v1_xboole_0(esk2_1(X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))))&(v4_pre_topc(esk2_1(X20),X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.21/0.41  fof(c_0_16, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.41  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_18, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  fof(c_0_19, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.41  cnf(c_0_20, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_21, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r2_hidden(X2,esk2_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.41  cnf(c_0_22, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.41  cnf(c_0_23, plain, (v2_struct_0(X1)|~v1_xboole_0(esk2_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  fof(c_0_24, plain, ![X22, X23]:(v1_xboole_0(X22)|~m1_subset_1(X23,X22)|m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.21/0.41  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r2_hidden(X2,esk2_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.21/0.41  cnf(c_0_26, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.41  cnf(c_0_27, plain, (v2_struct_0(X1)|r2_hidden(esk1_1(esk2_1(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.21/0.41  fof(c_0_28, plain, ![X24, X25]:(v1_xboole_0(X24)|~m1_subset_1(X25,X24)|k6_domain_1(X24,X25)=k1_tarski(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.21/0.41  fof(c_0_29, plain, ![X30, X31]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,u1_struct_0(X30))|v2_tex_2(k6_domain_1(u1_struct_0(X30),X31),X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.21/0.41  fof(c_0_30, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1))))), inference(assume_negation,[status(cth)],[t46_tex_2])).
% 0.21/0.41  fof(c_0_31, plain, ![X26, X27, X28]:(((v2_tex_2(X27,X26)|~v3_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(~v2_tex_2(X28,X26)|~r1_tarski(X27,X28)|X27=X28)|~v3_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26)))&((m1_subset_1(esk3_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))|~v2_tex_2(X27,X26)|v3_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(((v2_tex_2(esk3_2(X26,X27),X26)|~v2_tex_2(X27,X26)|v3_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(r1_tarski(X27,esk3_2(X26,X27))|~v2_tex_2(X27,X26)|v3_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26)))&(X27!=esk3_2(X26,X27)|~v2_tex_2(X27,X26)|v3_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.21/0.41  fof(c_0_32, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.41  fof(c_0_33, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.41  cnf(c_0_34, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.41  cnf(c_0_35, plain, (v2_struct_0(X1)|m1_subset_1(esk1_1(esk2_1(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_23])).
% 0.21/0.41  cnf(c_0_36, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.41  cnf(c_0_37, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.41  fof(c_0_38, plain, ![X11, X12]:k2_xboole_0(k1_tarski(X11),X12)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.21/0.41  fof(c_0_39, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.21/0.41  cnf(c_0_40, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.41  fof(c_0_41, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.21/0.41  fof(c_0_42, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&v3_tex_2(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).
% 0.21/0.41  cnf(c_0_43, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.41  cnf(c_0_44, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.41  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.41  cnf(c_0_46, plain, (v2_struct_0(X1)|m1_subset_1(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.21/0.41  cnf(c_0_47, plain, (k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(X1)))=k1_tarski(esk1_1(esk2_1(X1)))|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_35]), c_0_36])).
% 0.21/0.41  cnf(c_0_48, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.41  cnf(c_0_49, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.41  cnf(c_0_50, plain, (v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(X1))),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.21/0.41  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_53, plain, (X1=k1_xboole_0|~v2_tex_2(X1,X2)|~v3_tex_2(k1_xboole_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.21/0.41  cnf(c_0_54, plain, (v2_struct_0(X1)|m1_subset_1(k1_tarski(esk1_1(esk2_1(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.41  cnf(c_0_55, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.41  cnf(c_0_56, plain, (v2_tex_2(k1_tarski(esk1_1(esk2_1(X1))),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_47])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (v3_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.41  cnf(c_0_59, plain, (v2_struct_0(X1)|~v3_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (v3_tex_2(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])]), c_0_63]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 65
% 0.21/0.41  # Proof object clause steps            : 36
% 0.21/0.41  # Proof object formula steps           : 29
% 0.21/0.41  # Proof object conjectures             : 11
% 0.21/0.41  # Proof object clause conjectures      : 8
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 20
% 0.21/0.41  # Proof object initial formulas used   : 14
% 0.21/0.41  # Proof object generating inferences   : 15
% 0.21/0.41  # Proof object simplifying inferences  : 13
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 14
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 27
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 27
% 0.21/0.41  # Processed clauses                    : 158
% 0.21/0.41  # ...of these trivial                  : 1
% 0.21/0.41  # ...subsumed                          : 21
% 0.21/0.41  # ...remaining for further processing  : 136
% 0.21/0.41  # Other redundant clauses eliminated   : 0
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 1
% 0.21/0.41  # Backward-rewritten                   : 3
% 0.21/0.41  # Generated clauses                    : 190
% 0.21/0.41  # ...of the previous two non-trivial   : 184
% 0.21/0.41  # Contextual simplify-reflections      : 5
% 0.21/0.41  # Paramodulations                      : 190
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 0
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 105
% 0.21/0.41  #    Positive orientable unit clauses  : 9
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 3
% 0.21/0.41  #    Non-unit-clauses                  : 93
% 0.21/0.41  # Current number of unprocessed clauses: 80
% 0.21/0.41  # ...number of literals in the above   : 420
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 31
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 1719
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 361
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 27
% 0.21/0.41  # Unit Clause-clause subsumption calls : 9
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 1
% 0.21/0.41  # BW rewrite match successes           : 1
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 7670
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.057 s
% 0.21/0.41  # System time              : 0.008 s
% 0.21/0.41  # Total time               : 0.064 s
% 0.21/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
