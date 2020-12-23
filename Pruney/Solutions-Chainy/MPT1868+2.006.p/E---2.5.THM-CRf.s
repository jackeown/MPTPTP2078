%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 431 expanded)
%              Number of clauses        :   61 ( 185 expanded)
%              Number of leaves         :   14 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  402 (2028 expanded)
%              Number of equality atoms :   42 ( 227 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_tex_2(X1,X2)
              <=> u1_struct_0(X3) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(t10_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & X2 = u1_struct_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t36_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t24_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v2_pre_topc(k1_tex_2(X1,X2))
           => ( v1_tdlat_3(k1_tex_2(X1,X2))
              & v2_tdlat_3(k1_tex_2(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_14,plain,(
    ! [X26,X27,X28] :
      ( ( X28 != k1_tex_2(X26,X27)
        | u1_struct_0(X28) = k6_domain_1(u1_struct_0(X26),X27)
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26) )
      & ( u1_struct_0(X28) != k6_domain_1(u1_struct_0(X26),X27)
        | X28 = k1_tex_2(X26,X27)
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

fof(c_0_15,plain,(
    ! [X29,X30] :
      ( ( ~ v2_struct_0(esk3_2(X29,X30))
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_pre_topc(esk3_2(X29,X30))
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_pre_topc(esk3_2(X29,X30),X29)
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29) )
      & ( X30 = u1_struct_0(esk3_2(X29,X30))
        | v1_xboole_0(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | v2_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_17,plain,
    ( X1 = k1_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(X1) != k6_domain_1(u1_struct_0(X2),X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_pre_topc(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_23,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( esk3_2(X1,k6_domain_1(u1_struct_0(X2),X3)) = k1_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X2),X3))
    | ~ m1_pre_topc(esk3_2(X1,k6_domain_1(u1_struct_0(X2),X3)),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t36_tex_2])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_pre_topc(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( esk3_2(X1,k6_domain_1(u1_struct_0(X1),X2)) = k1_tex_2(X1,X2)
    | v2_struct_0(X1)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_32,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | k6_domain_1(X24,X25) = k1_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_33,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ v2_tex_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

fof(c_0_36,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_xboole_0(u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_37,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_pre_topc(k1_tex_2(X1,X2))
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_43,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
    ! [X32,X33] :
      ( ( v1_tdlat_3(k1_tex_2(X32,X33))
        | ~ v2_pre_topc(k1_tex_2(X32,X33))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32) )
      & ( v2_tdlat_3(k1_tex_2(X32,X33))
        | ~ v2_pre_topc(k1_tex_2(X32,X33))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tex_2])])])])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | v2_pre_topc(k1_tex_2(X1,X2))
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_52,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v2_tex_2(X36,X34)
        | v1_tdlat_3(X35)
        | X36 != u1_struct_0(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ v1_tdlat_3(X35)
        | v2_tex_2(X36,X34)
        | X36 != u1_struct_0(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

cnf(c_0_53,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( ~ l1_struct_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( v1_tdlat_3(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v2_pre_topc(k1_tex_2(X1,X2))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

fof(c_0_58,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X17,X16)
        | r2_hidden(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ r2_hidden(X17,X16)
        | m1_subset_1(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ m1_subset_1(X17,X16)
        | v1_xboole_0(X17)
        | ~ v1_xboole_0(X16) )
      & ( ~ v1_xboole_0(X17)
        | m1_subset_1(X17,X16)
        | ~ v1_xboole_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_59,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = k2_tarski(X2,X2)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_63,plain,
    ( v1_tdlat_3(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_69,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk4_0,esk5_0)) = k2_tarski(esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_47])]),c_0_44]),c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( v1_tdlat_3(k1_tex_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_47]),c_0_64])]),c_0_44]),c_0_62])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_51])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_39])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_tex_2(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_50]),c_0_61])]),c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( v2_tex_2(k2_tarski(esk5_0,esk5_0),X1)
    | v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k1_tex_2(esk4_0,esk5_0),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_77,plain,
    ( r2_hidden(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_39]),c_0_73])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_50]),c_0_51])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk4_0,esk5_0))
    | ~ m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_47])]),c_0_44])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_82,plain,
    ( r2_hidden(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_50])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_39])).

cnf(c_0_84,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_47]),c_0_61])]),c_0_44]),c_0_62])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_81,c_0_41])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_61]),c_0_62])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_51])).

cnf(c_0_88,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_61]),c_0_47])]),c_0_44]),c_0_88]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.029 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 0.13/0.40  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.13/0.40  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.13/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.40  fof(t36_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 0.13/0.40  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.40  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.40  fof(t24_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v2_pre_topc(k1_tex_2(X1,X2))=>(v1_tdlat_3(k1_tex_2(X1,X2))&v2_tdlat_3(k1_tex_2(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tex_2)).
% 0.13/0.40  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 0.13/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.40  fof(c_0_14, plain, ![X26, X27, X28]:((X28!=k1_tex_2(X26,X27)|u1_struct_0(X28)=k6_domain_1(u1_struct_0(X26),X27)|(v2_struct_0(X28)|~v1_pre_topc(X28)|~m1_pre_topc(X28,X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~l1_pre_topc(X26)))&(u1_struct_0(X28)!=k6_domain_1(u1_struct_0(X26),X27)|X28=k1_tex_2(X26,X27)|(v2_struct_0(X28)|~v1_pre_topc(X28)|~m1_pre_topc(X28,X26))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X29, X30]:((((~v2_struct_0(esk3_2(X29,X30))|(v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))|(v2_struct_0(X29)|~l1_pre_topc(X29)))&(v1_pre_topc(esk3_2(X29,X30))|(v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))|(v2_struct_0(X29)|~l1_pre_topc(X29))))&(m1_pre_topc(esk3_2(X29,X30),X29)|(v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))|(v2_struct_0(X29)|~l1_pre_topc(X29))))&(X30=u1_struct_0(esk3_2(X29,X30))|(v1_xboole_0(X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))|(v2_struct_0(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.13/0.40  fof(c_0_16, plain, ![X18, X19]:(~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|v2_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.13/0.40  cnf(c_0_17, plain, (X1=k1_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|u1_struct_0(X1)!=k6_domain_1(u1_struct_0(X2),X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_18, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_19, plain, (v1_pre_topc(esk3_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_20, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_21, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.40  fof(c_0_22, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.40  cnf(c_0_23, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_24, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_25, plain, (esk3_2(X1,k6_domain_1(u1_struct_0(X2),X3))=k1_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v1_xboole_0(k6_domain_1(u1_struct_0(X2),X3))|~m1_pre_topc(esk3_2(X1,k6_domain_1(u1_struct_0(X2),X3)),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(X2),X3),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18])]), c_0_19]), c_0_20])).
% 0.13/0.40  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  fof(c_0_28, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)))), inference(assume_negation,[status(cth)],[t36_tex_2])).
% 0.13/0.40  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_pre_topc(esk3_2(X1,X2))|v1_xboole_0(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_30, plain, (esk3_2(X1,k6_domain_1(u1_struct_0(X1),X2))=k1_tex_2(X1,X2)|v2_struct_0(X1)|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.13/0.40  fof(c_0_31, plain, ![X22, X23]:(v1_xboole_0(X22)|~m1_subset_1(X23,X22)|m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.40  fof(c_0_32, plain, ![X24, X25]:(v1_xboole_0(X24)|~m1_subset_1(X25,X24)|k6_domain_1(X24,X25)=k1_tarski(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.40  fof(c_0_33, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.40  fof(c_0_35, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&~v2_tex_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 0.13/0.40  fof(c_0_36, plain, ![X21]:(v2_struct_0(X21)|~l1_struct_0(X21)|~v1_xboole_0(u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.40  fof(c_0_37, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.40  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_pre_topc(k1_tex_2(X1,X2))|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.40  cnf(c_0_39, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_40, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_42, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.13/0.40  cnf(c_0_43, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_18, c_0_30])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_45, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.40  cnf(c_0_46, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  fof(c_0_48, plain, ![X32, X33]:((v1_tdlat_3(k1_tex_2(X32,X33))|~v2_pre_topc(k1_tex_2(X32,X33))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~l1_pre_topc(X32)))&(v2_tdlat_3(k1_tex_2(X32,X33))|~v2_pre_topc(k1_tex_2(X32,X33))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tex_2])])])])])).
% 0.13/0.40  cnf(c_0_49, plain, (v2_struct_0(X1)|v2_pre_topc(k1_tex_2(X1,X2))|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.40  cnf(c_0_50, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_40, c_0_27])).
% 0.13/0.40  cnf(c_0_51, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.40  fof(c_0_52, plain, ![X34, X35, X36]:((~v2_tex_2(X36,X34)|v1_tdlat_3(X35)|X36!=u1_struct_0(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|(v2_struct_0(X35)|~m1_pre_topc(X35,X34))|(v2_struct_0(X34)|~l1_pre_topc(X34)))&(~v1_tdlat_3(X35)|v2_tex_2(X36,X34)|X36!=u1_struct_0(X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|(v2_struct_0(X35)|~m1_pre_topc(X35,X34))|(v2_struct_0(X34)|~l1_pre_topc(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.13/0.40  cnf(c_0_53, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_43, c_0_39])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (~l1_struct_0(esk4_0)|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.40  cnf(c_0_56, plain, (v1_tdlat_3(k1_tex_2(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.40  cnf(c_0_57, plain, (v2_struct_0(X1)|v2_pre_topc(k1_tex_2(X1,X2))|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.13/0.40  fof(c_0_58, plain, ![X16, X17]:(((~m1_subset_1(X17,X16)|r2_hidden(X17,X16)|v1_xboole_0(X16))&(~r2_hidden(X17,X16)|m1_subset_1(X17,X16)|v1_xboole_0(X16)))&((~m1_subset_1(X17,X16)|v1_xboole_0(X17)|~v1_xboole_0(X16))&(~v1_xboole_0(X17)|m1_subset_1(X17,X16)|~v1_xboole_0(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.40  cnf(c_0_59, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.40  cnf(c_0_60, plain, (u1_struct_0(k1_tex_2(X1,X2))=k2_tarski(X2,X2)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_51])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.13/0.40  cnf(c_0_63, plain, (v1_tdlat_3(k1_tex_2(X1,X2))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_65, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.40  cnf(c_0_66, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_50])).
% 0.13/0.40  cnf(c_0_67, plain, (v2_struct_0(X1)|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_20, c_0_30])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (~v2_tex_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_69, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_59])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (u1_struct_0(k1_tex_2(esk4_0,esk5_0))=k2_tarski(esk5_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_47])]), c_0_44]), c_0_62])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (v1_tdlat_3(k1_tex_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_61]), c_0_47]), c_0_64])]), c_0_44]), c_0_62])).
% 0.13/0.40  cnf(c_0_72, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.40  cnf(c_0_73, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_xboole_0(k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_51])).
% 0.13/0.40  cnf(c_0_74, plain, (v2_struct_0(X1)|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_67, c_0_39])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (~v2_tex_2(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_50]), c_0_61])]), c_0_62])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (v2_tex_2(k2_tarski(esk5_0,esk5_0),X1)|v2_struct_0(k1_tex_2(esk4_0,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(k1_tex_2(esk4_0,esk5_0),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.13/0.40  cnf(c_0_77, plain, (r2_hidden(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_39]), c_0_73])).
% 0.13/0.40  cnf(c_0_78, plain, (v2_struct_0(X1)|m1_pre_topc(k1_tex_2(X1,X2),X1)|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_24, c_0_30])).
% 0.13/0.40  cnf(c_0_79, plain, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_50]), c_0_51])).
% 0.13/0.40  cnf(c_0_80, negated_conjecture, (v2_struct_0(k1_tex_2(esk4_0,esk5_0))|~m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_47])]), c_0_44])).
% 0.13/0.40  cnf(c_0_81, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.40  cnf(c_0_82, plain, (r2_hidden(k2_tarski(X1,X1),k1_zfmisc_1(X2))|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_77, c_0_50])).
% 0.13/0.40  cnf(c_0_83, plain, (v2_struct_0(X1)|m1_pre_topc(k1_tex_2(X1,X2),X1)|v1_xboole_0(k6_domain_1(u1_struct_0(X1),X2))|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_78, c_0_39])).
% 0.13/0.40  cnf(c_0_84, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_47]), c_0_61])]), c_0_44]), c_0_62])).
% 0.13/0.40  cnf(c_0_85, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_81, c_0_41])).
% 0.13/0.40  cnf(c_0_86, negated_conjecture, (r2_hidden(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_61]), c_0_62])).
% 0.13/0.40  cnf(c_0_87, plain, (v2_struct_0(X1)|m1_pre_topc(k1_tex_2(X1,X2),X1)|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_51])).
% 0.13/0.40  cnf(c_0_88, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 0.13/0.40  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_61]), c_0_47])]), c_0_44]), c_0_88]), c_0_62]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 90
% 0.13/0.40  # Proof object clause steps            : 61
% 0.13/0.40  # Proof object formula steps           : 29
% 0.13/0.40  # Proof object conjectures             : 20
% 0.13/0.40  # Proof object clause conjectures      : 17
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 23
% 0.13/0.40  # Proof object initial formulas used   : 14
% 0.13/0.40  # Proof object generating inferences   : 32
% 0.13/0.40  # Proof object simplifying inferences  : 47
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 31
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 30
% 0.13/0.40  # Processed clauses                    : 259
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 51
% 0.13/0.40  # ...remaining for further processing  : 208
% 0.13/0.40  # Other redundant clauses eliminated   : 13
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 18
% 0.13/0.40  # Backward-rewritten                   : 4
% 0.13/0.40  # Generated clauses                    : 418
% 0.13/0.40  # ...of the previous two non-trivial   : 357
% 0.13/0.40  # Contextual simplify-reflections      : 45
% 0.13/0.40  # Paramodulations                      : 402
% 0.13/0.40  # Factorizations                       : 2
% 0.13/0.40  # Equation resolutions                 : 14
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 150
% 0.13/0.40  #    Positive orientable unit clauses  : 13
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 16
% 0.13/0.40  #    Non-unit-clauses                  : 121
% 0.13/0.40  # Current number of unprocessed clauses: 153
% 0.13/0.40  # ...number of literals in the above   : 1108
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 54
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 5404
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 764
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 93
% 0.13/0.40  # Unit Clause-clause subsumption calls : 73
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 5
% 0.13/0.40  # BW rewrite match successes           : 4
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 14530
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.051 s
% 0.13/0.40  # System time              : 0.008 s
% 0.13/0.40  # Total time               : 0.059 s
% 0.13/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
