%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:31 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 441 expanded)
%              Number of clauses        :   46 ( 159 expanded)
%              Number of leaves         :   14 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  292 (1977 expanded)
%              Number of equality atoms :   10 (  31 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_tex_2(k1_tex_2(X1,X2),X1)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(cc6_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ v1_xboole_0(X2)
           => ( ~ v1_xboole_0(X2)
              & ~ v1_subset_1(X2,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t9_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(t6_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_15,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(X4)
      | l1_struct_0(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) )
    & ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_tex_2(X14,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | X15 != u1_struct_0(X14)
        | v1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk1_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))
        | v1_tex_2(X14,X13)
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X13) )
      & ( esk1_2(X13,X14) = u1_struct_0(X14)
        | v1_tex_2(X14,X13)
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ v1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))
        | v1_tex_2(X14,X13)
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_18,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X25),X26),u1_struct_0(X25))
      | ~ v7_struct_0(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ( ~ v2_struct_0(k1_tex_2(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( v1_pre_topc(k1_tex_2(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) )
      & ( m1_pre_topc(k1_tex_2(X19,X20),X19)
        | v2_struct_0(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_30,plain,(
    ! [X7] :
      ( v2_struct_0(X7)
      | ~ l1_struct_0(X7)
      | ~ v1_xboole_0(u1_struct_0(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_31,plain,(
    ! [X11,X12] :
      ( ( ~ v1_xboole_0(X12)
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v7_struct_0(X11)
        | ~ l1_struct_0(X11) )
      & ( ~ v1_subset_1(X12,u1_struct_0(X11))
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v2_struct_0(X11)
        | ~ v7_struct_0(X11)
        | ~ l1_struct_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tex_2])])])])])).

cnf(c_0_32,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v7_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27]),c_0_28])])).

fof(c_0_34,plain,(
    ! [X5,X6] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_pre_topc(X6,X5)
      | l1_pre_topc(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v7_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))
    | ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_40,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | v7_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | v1_subset_1(k6_domain_1(u1_struct_0(X27),X28),u1_struct_0(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tex_2])])])])).

fof(c_0_43,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X23)
      | ~ m1_subset_1(X24,X23)
      | ~ v1_subset_1(k6_domain_1(X23,X24),X23)
      | ~ v1_zfmisc_1(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))
    | ~ l1_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(esk2_0,esk3_0)))
    | ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_28])]),c_0_27]),c_0_39])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X2),X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_28])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26]),c_0_21])]),c_0_27])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | ~ v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26])]),c_0_27]),c_0_28])])).

cnf(c_0_56,plain,
    ( v1_tex_2(X1,X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ v1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_25]),c_0_26])]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ v7_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26]),c_0_21])]),c_0_27])).

fof(c_0_59,plain,(
    ! [X17,X18] :
      ( ( ~ v1_subset_1(X18,X17)
        | X18 != X17
        | ~ m1_subset_1(X18,k1_zfmisc_1(X17)) )
      & ( X18 = X17
        | v1_subset_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_60,negated_conjecture,
    ( v7_struct_0(esk2_0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_21])])).

cnf(c_0_61,negated_conjecture,
    ( v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))
    | ~ v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_57]),c_0_21])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v7_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_26]),c_0_21])]),c_0_27])).

fof(c_0_63,plain,(
    ! [X8] :
      ( ~ v7_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_zfmisc_1(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_64,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) = u1_struct_0(esk2_0)
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_64]),c_0_62]),c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_41]),c_0_26]),c_0_21])]),c_0_27])).

fof(c_0_69,plain,(
    ! [X21,X22] :
      ( ( ~ v2_struct_0(k1_tex_2(X21,X22))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) )
      & ( v7_struct_0(k1_tex_2(X21,X22))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) )
      & ( v1_pre_topc(k1_tex_2(X21,X22))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_subset_1(X22,u1_struct_0(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v7_struct_0(k1_tex_2(esk2_0,esk3_0))
    | ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_71,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_26]),c_0_21])]),c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_26]),c_0_21])]),c_0_27])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_41]),c_0_26]),c_0_21])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.14/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.14/0.38  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.14/0.38  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.14/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.38  fof(cc6_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~(v1_xboole_0(X2))=>(~(v1_xboole_0(X2))&~(v1_subset_1(X2,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tex_2)).
% 0.14/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.14/0.38  fof(t9_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&~(v7_struct_0(X1)))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 0.14/0.38  fof(t6_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.14/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.14/0.38  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.14/0.38  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.14/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.14/0.38  fof(c_0_15, plain, ![X4]:(~l1_pre_topc(X4)|l1_struct_0(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  fof(c_0_16, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&((~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))&(v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.14/0.38  fof(c_0_17, plain, ![X13, X14, X15]:((~v1_tex_2(X14,X13)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))|(X15!=u1_struct_0(X14)|v1_subset_1(X15,u1_struct_0(X13))))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X13))&((m1_subset_1(esk1_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))|v1_tex_2(X14,X13)|~m1_pre_topc(X14,X13)|~l1_pre_topc(X13))&((esk1_2(X13,X14)=u1_struct_0(X14)|v1_tex_2(X14,X13)|~m1_pre_topc(X14,X13)|~l1_pre_topc(X13))&(~v1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))|v1_tex_2(X14,X13)|~m1_pre_topc(X14,X13)|~l1_pre_topc(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.14/0.38  fof(c_0_18, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|m1_subset_1(u1_struct_0(X10),k1_zfmisc_1(u1_struct_0(X9))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.14/0.38  fof(c_0_19, plain, ![X25, X26]:(v2_struct_0(X25)|~l1_struct_0(X25)|(~m1_subset_1(X26,u1_struct_0(X25))|(~v1_subset_1(k6_domain_1(u1_struct_0(X25),X26),u1_struct_0(X25))|~v7_struct_0(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.14/0.38  cnf(c_0_20, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_22, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_23, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_24, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  fof(c_0_29, plain, ![X19, X20]:(((~v2_struct_0(k1_tex_2(X19,X20))|(v2_struct_0(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))))&(v1_pre_topc(k1_tex_2(X19,X20))|(v2_struct_0(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19)))))&(m1_pre_topc(k1_tex_2(X19,X20),X19)|(v2_struct_0(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.14/0.38  fof(c_0_30, plain, ![X7]:(v2_struct_0(X7)|~l1_struct_0(X7)|~v1_xboole_0(u1_struct_0(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.38  fof(c_0_31, plain, ![X11, X12]:((~v1_xboole_0(X12)|v1_xboole_0(X12)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v7_struct_0(X11)|~l1_struct_0(X11)))&(~v1_subset_1(X12,u1_struct_0(X11))|v1_xboole_0(X12)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|(v2_struct_0(X11)|~v7_struct_0(X11)|~l1_struct_0(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tex_2])])])])])).
% 0.14/0.38  cnf(c_0_32, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v7_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])]), c_0_27]), c_0_28])])).
% 0.14/0.38  fof(c_0_34, plain, ![X5, X6]:(~l1_pre_topc(X5)|(~m1_pre_topc(X6,X5)|l1_pre_topc(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.14/0.38  cnf(c_0_35, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_36, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_37, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|~v1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v7_struct_0(X2)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))|~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_21])])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.14/0.38  cnf(c_0_40, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_41, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  fof(c_0_42, plain, ![X27, X28]:(v2_struct_0(X27)|v7_struct_0(X27)|~l1_struct_0(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|v1_subset_1(k6_domain_1(u1_struct_0(X27),X28),u1_struct_0(X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tex_2])])])])).
% 0.14/0.38  fof(c_0_43, plain, ![X23, X24]:(v1_xboole_0(X23)|(~m1_subset_1(X24,X23)|(~v1_subset_1(k6_domain_1(X23,X24),X23)|~v1_zfmisc_1(X23)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_tex_2])])])])).
% 0.14/0.38  cnf(c_0_44, plain, (v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(u1_struct_0(k1_tex_2(X1,X2)))|~l1_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (v1_xboole_0(u1_struct_0(k1_tex_2(esk2_0,esk3_0)))|~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_28])]), c_0_27]), c_0_39])).
% 0.14/0.38  cnf(c_0_46, plain, (v2_struct_0(X1)|l1_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_48, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_49, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_50, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_51, plain, (v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~v1_subset_1(k6_domain_1(X1,X2),X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_36]), c_0_28])])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26]), c_0_21])]), c_0_27])).
% 0.14/0.38  cnf(c_0_54, plain, (v2_struct_0(X1)|l1_struct_0(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_46])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (v7_struct_0(esk2_0)|~v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_26])]), c_0_27]), c_0_28])])).
% 0.14/0.38  cnf(c_0_56, plain, (v1_tex_2(X1,X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (v1_tex_2(k1_tex_2(esk2_0,esk3_0),esk2_0)|~v1_zfmisc_1(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_25]), c_0_26])]), c_0_52])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (~v7_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_26]), c_0_21])]), c_0_27])).
% 0.14/0.38  fof(c_0_59, plain, ![X17, X18]:((~v1_subset_1(X18,X17)|X18!=X17|~m1_subset_1(X18,k1_zfmisc_1(X17)))&(X18=X17|v1_subset_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (v7_struct_0(esk2_0)|~v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_21])])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (v1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),u1_struct_0(esk2_0))|~v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_57]), c_0_21])])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (~v7_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_26]), c_0_21])]), c_0_27])).
% 0.14/0.38  fof(c_0_63, plain, ![X8]:(~v7_struct_0(X8)|~l1_struct_0(X8)|v1_zfmisc_1(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.14/0.38  cnf(c_0_64, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk2_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.14/0.38  cnf(c_0_66, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))=u1_struct_0(esk2_0)|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_64]), c_0_62]), c_0_39])).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, (~v1_zfmisc_1(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_41]), c_0_26]), c_0_21])]), c_0_27])).
% 0.14/0.38  fof(c_0_69, plain, ![X21, X22]:(((~v2_struct_0(k1_tex_2(X21,X22))|(v2_struct_0(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21))))&(v7_struct_0(k1_tex_2(X21,X22))|(v2_struct_0(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21)))))&(v1_pre_topc(k1_tex_2(X21,X22))|(v2_struct_0(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.14/0.38  cnf(c_0_70, negated_conjecture, (~v7_struct_0(k1_tex_2(esk2_0,esk3_0))|~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.14/0.38  cnf(c_0_71, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_26]), c_0_21])]), c_0_27])).
% 0.14/0.38  cnf(c_0_73, negated_conjecture, (~m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_54]), c_0_26]), c_0_21])]), c_0_27])).
% 0.14/0.38  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_41]), c_0_26]), c_0_21])]), c_0_27]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 75
% 0.14/0.38  # Proof object clause steps            : 46
% 0.14/0.38  # Proof object formula steps           : 29
% 0.14/0.38  # Proof object conjectures             : 28
% 0.14/0.38  # Proof object clause conjectures      : 25
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 21
% 0.14/0.38  # Proof object initial formulas used   : 14
% 0.14/0.38  # Proof object generating inferences   : 24
% 0.14/0.38  # Proof object simplifying inferences  : 59
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 14
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 27
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 26
% 0.14/0.38  # Processed clauses                    : 92
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 8
% 0.14/0.38  # ...remaining for further processing  : 84
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 5
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 64
% 0.14/0.38  # ...of the previous two non-trivial   : 56
% 0.14/0.38  # Contextual simplify-reflections      : 5
% 0.14/0.38  # Paramodulations                      : 62
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 52
% 0.14/0.38  #    Positive orientable unit clauses  : 4
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 6
% 0.14/0.38  #    Non-unit-clauses                  : 42
% 0.14/0.38  # Current number of unprocessed clauses: 14
% 0.14/0.38  # ...number of literals in the above   : 71
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 30
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 367
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 168
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.14/0.38  # Unit Clause-clause subsumption calls : 31
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3859
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.031 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.037 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
