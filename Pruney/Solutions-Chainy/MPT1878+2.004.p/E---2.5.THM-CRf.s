%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 105 expanded)
%              Number of clauses        :   32 (  44 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  203 ( 431 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t46_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_14,plain,(
    ! [X32,X33,X34] :
      ( ( v2_tex_2(X33,X32)
        | ~ v3_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ v2_tex_2(X34,X32)
        | ~ r1_tarski(X33,X34)
        | X33 = X34
        | ~ v3_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk4_2(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))
        | ~ v2_tex_2(X33,X32)
        | v3_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( v2_tex_2(esk4_2(X32,X33),X32)
        | ~ v2_tex_2(X33,X32)
        | v3_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( r1_tarski(X33,esk4_2(X32,X33))
        | ~ v2_tex_2(X33,X32)
        | v3_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) )
      & ( X33 != esk4_2(X32,X33)
        | ~ v2_tex_2(X33,X32)
        | v3_tex_2(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_15,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_16,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_17,plain,(
    ! [X11,X12] : k2_xboole_0(k1_tarski(X11),X12) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_19,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | m1_subset_1(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_20,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_xboole_0(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_22,plain,(
    ! [X28] :
      ( ( m1_subset_1(esk3_1(X28),k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v1_xboole_0(esk3_1(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v4_pre_topc(esk3_1(X28),X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

cnf(c_0_23,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(k1_tarski(X19),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | v2_tex_2(k6_domain_1(u1_struct_0(X36),X37),X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk3_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ m1_subset_1(X31,X30)
      | k6_domain_1(X30,X31) = k1_tarski(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ~ v3_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t46_tex_2])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(k1_xboole_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_xboole_0(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & v3_tex_2(esk6_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).

cnf(c_0_46,plain,
    ( ~ v2_tex_2(k1_tarski(X1),X2)
    | ~ v3_tex_2(k1_xboole_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(u1_struct_0(X1))),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,plain,
    ( k6_domain_1(X1,esk1_1(X1)) = k1_tarski(esk1_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_tex_2(k1_tarski(esk1_1(u1_struct_0(X1))),X1)
    | ~ v3_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_52,plain,
    ( v2_tex_2(k1_tarski(esk1_1(u1_struct_0(X1))),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( v3_tex_2(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ v3_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( v3_tex_2(k1_xboole_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.20/0.43  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 0.20/0.43  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.43  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.20/0.43  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.43  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.43  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.20/0.43  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.20/0.43  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.20/0.43  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.43  fof(t46_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 0.20/0.43  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.43  fof(c_0_14, plain, ![X32, X33, X34]:(((v2_tex_2(X33,X32)|~v3_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|(~v2_tex_2(X34,X32)|~r1_tarski(X33,X34)|X33=X34)|~v3_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32)))&((m1_subset_1(esk4_2(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))|~v2_tex_2(X33,X32)|v3_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(((v2_tex_2(esk4_2(X32,X33),X32)|~v2_tex_2(X33,X32)|v3_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))&(r1_tarski(X33,esk4_2(X32,X33))|~v2_tex_2(X33,X32)|v3_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32)))&(X33!=esk4_2(X32,X33)|~v2_tex_2(X33,X32)|v3_tex_2(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~l1_pre_topc(X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.20/0.43  fof(c_0_15, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.43  fof(c_0_16, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.43  fof(c_0_17, plain, ![X11, X12]:k2_xboole_0(k1_tarski(X11),X12)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.20/0.43  fof(c_0_18, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.43  fof(c_0_19, plain, ![X23, X24]:(~r2_hidden(X23,X24)|m1_subset_1(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.43  fof(c_0_20, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  fof(c_0_21, plain, ![X21, X22]:(~v1_xboole_0(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_xboole_0(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.43  fof(c_0_22, plain, ![X28]:(((m1_subset_1(esk3_1(X28),k1_zfmisc_1(u1_struct_0(X28)))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(~v1_xboole_0(esk3_1(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))))&(v4_pre_topc(esk3_1(X28),X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.20/0.43  cnf(c_0_23, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_24, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  fof(c_0_26, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(k1_tarski(X19),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.20/0.43  cnf(c_0_27, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  fof(c_0_29, plain, ![X36, X37]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_subset_1(X37,u1_struct_0(X36))|v2_tex_2(k6_domain_1(u1_struct_0(X36),X37),X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.20/0.43  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_31, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_32, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_33, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_34, plain, (v2_struct_0(X1)|~v1_xboole_0(esk3_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  fof(c_0_35, plain, ![X30, X31]:(v1_xboole_0(X30)|~m1_subset_1(X31,X30)|k6_domain_1(X30,X31)=k1_tarski(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.43  fof(c_0_36, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1))))), inference(assume_negation,[status(cth)],[t46_tex_2])).
% 0.20/0.43  cnf(c_0_37, plain, (X1=k1_xboole_0|~v2_tex_2(X1,X2)|~v3_tex_2(k1_xboole_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.20/0.43  cnf(c_0_38, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_39, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.43  cnf(c_0_40, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_41, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.43  cnf(c_0_42, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.43  cnf(c_0_43, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  fof(c_0_44, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.43  fof(c_0_45, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&v3_tex_2(esk6_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).
% 0.20/0.43  cnf(c_0_46, plain, (~v2_tex_2(k1_tarski(X1),X2)|~v3_tex_2(k1_xboole_0,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.43  cnf(c_0_47, plain, (v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(u1_struct_0(X1))),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.20/0.43  cnf(c_0_48, plain, (k6_domain_1(X1,esk1_1(X1))=k1_tarski(esk1_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_43, c_0_41])).
% 0.20/0.43  cnf(c_0_49, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.43  cnf(c_0_51, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_tex_2(k1_tarski(esk1_1(u1_struct_0(X1))),X1)|~v3_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 0.20/0.43  cnf(c_0_52, plain, (v2_tex_2(k1_tarski(esk1_1(u1_struct_0(X1))),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_42])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (v3_tex_2(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.43  cnf(c_0_55, plain, (v2_struct_0(X1)|~v3_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_42])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (v3_tex_2(k1_xboole_0,esk5_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])]), c_0_59]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 61
% 0.20/0.43  # Proof object clause steps            : 32
% 0.20/0.43  # Proof object formula steps           : 29
% 0.20/0.43  # Proof object conjectures             : 11
% 0.20/0.43  # Proof object clause conjectures      : 8
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 19
% 0.20/0.43  # Proof object initial formulas used   : 14
% 0.20/0.43  # Proof object generating inferences   : 12
% 0.20/0.43  # Proof object simplifying inferences  : 12
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 17
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 31
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 31
% 0.20/0.43  # Processed clauses                    : 481
% 0.20/0.43  # ...of these trivial                  : 1
% 0.20/0.43  # ...subsumed                          : 213
% 0.20/0.43  # ...remaining for further processing  : 267
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 8
% 0.20/0.43  # Backward-rewritten                   : 3
% 0.20/0.43  # Generated clauses                    : 1769
% 0.20/0.43  # ...of the previous two non-trivial   : 1260
% 0.20/0.43  # Contextual simplify-reflections      : 22
% 0.20/0.43  # Paramodulations                      : 1769
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 225
% 0.20/0.43  #    Positive orientable unit clauses  : 9
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 3
% 0.20/0.43  #    Non-unit-clauses                  : 213
% 0.20/0.43  # Current number of unprocessed clauses: 807
% 0.20/0.43  # ...number of literals in the above   : 4261
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 42
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 9601
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 2169
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 243
% 0.20/0.43  # Unit Clause-clause subsumption calls : 13
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 1
% 0.20/0.43  # BW rewrite match successes           : 1
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 38025
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.080 s
% 0.20/0.43  # System time              : 0.005 s
% 0.20/0.43  # Total time               : 0.085 s
% 0.20/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
