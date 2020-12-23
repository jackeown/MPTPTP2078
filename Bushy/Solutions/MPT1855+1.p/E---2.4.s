%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t23_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:29 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 277 expanded)
%              Number of clauses        :   45 ( 106 expanded)
%              Number of leaves         :   15 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 (1354 expanded)
%              Number of equality atoms :   34 ( 180 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v7_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t23_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',redefinition_k6_domain_1)).

fof(d1_tex_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ( v7_struct_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & u1_struct_0(X1) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',d1_tex_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',fc2_struct_0)).

fof(t5_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( u1_struct_0(X2) = u1_struct_0(X3)
               => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t5_tsep_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',dt_k6_domain_1)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',dt_k1_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',d4_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t4_subset)).

fof(l17_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',l17_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t5_subset)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',t37_zfmisc_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t23_tex_2.p',dt_l1_pre_topc)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v7_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tex_2])).

fof(c_0_16,plain,(
    ! [X42,X43] :
      ( v1_xboole_0(X42)
      | ~ m1_subset_1(X43,X42)
      | k6_domain_1(X42,X43) = k1_tarski(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_17,plain,(
    ! [X11,X13] :
      ( ( m1_subset_1(esk3_1(X11),u1_struct_0(X11))
        | ~ v7_struct_0(X11)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11) )
      & ( u1_struct_0(X11) = k6_domain_1(u1_struct_0(X11),esk3_1(X11))
        | ~ v7_struct_0(X11)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X11))
        | u1_struct_0(X11) != k6_domain_1(u1_struct_0(X11),X13)
        | v7_struct_0(X11)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_1])])])])])])).

fof(c_0_18,plain,(
    ! [X33] :
      ( v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | ~ v1_xboole_0(u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_19,plain,(
    ! [X58,X59,X60] :
      ( ~ l1_pre_topc(X58)
      | ~ m1_pre_topc(X59,X58)
      | ~ m1_pre_topc(X60,X58)
      | u1_struct_0(X59) != u1_struct_0(X60)
      | g1_pre_topc(u1_struct_0(X59),u1_pre_topc(X59)) = g1_pre_topc(u1_struct_0(X60),u1_pre_topc(X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_tsep_1])])])).

fof(c_0_20,negated_conjecture,(
    ! [X7] :
      ( ~ v2_struct_0(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & v7_struct_0(esk2_0)
      & m1_pre_topc(esk2_0,esk1_0)
      & ( ~ m1_subset_1(X7,u1_struct_0(esk1_0))
        | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk1_0,X7)),u1_pre_topc(k1_tex_2(esk1_0,X7))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X1),esk3_1(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X2) != u1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( u1_struct_0(X1) = k1_tarski(esk3_1(X1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v7_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v7_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk1_0,X1)),u1_pre_topc(k1_tex_2(esk1_0,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | u1_struct_0(X1) != u1_struct_0(esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_35,plain,(
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

fof(c_0_36,plain,(
    ! [X14,X15,X16] :
      ( ( X16 != k1_tex_2(X14,X15)
        | u1_struct_0(X16) = k6_domain_1(u1_struct_0(X14),X15)
        | v2_struct_0(X16)
        | ~ v1_pre_topc(X16)
        | ~ m1_pre_topc(X16,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14) )
      & ( u1_struct_0(X16) != k6_domain_1(u1_struct_0(X14),X15)
        | X16 = k1_tex_2(X14,X15)
        | v2_struct_0(X16)
        | ~ v1_pre_topc(X16)
        | ~ m1_pre_topc(X16,X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | v2_struct_0(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

fof(c_0_37,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | m1_subset_1(X52,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_38,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_pre_topc(X39,X38)
      | m1_subset_1(u1_struct_0(X39),k1_zfmisc_1(u1_struct_0(X38))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l17_tex_2])])])).

fof(c_0_39,plain,(
    ! [X50,X51] :
      ( ( ~ m1_subset_1(X50,k1_zfmisc_1(X51))
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(X50,X51)
        | m1_subset_1(X50,k1_zfmisc_1(X51)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_40,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v7_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_tarski(esk3_1(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_42,plain,(
    ! [X55,X56,X57] :
      ( ~ r2_hidden(X55,X56)
      | ~ m1_subset_1(X56,k1_zfmisc_1(X57))
      | ~ v1_xboole_0(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk1_0,X1)) != u1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_pre_topc(k1_tex_2(esk1_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_51,plain,(
    ! [X48,X49] :
      ( ( ~ r1_tarski(k1_tarski(X48),X49)
        | r2_hidden(X48,X49) )
      & ( ~ r2_hidden(X48,X49)
        | r1_tarski(k1_tarski(X48),X49) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk3_1(esk2_0)),k1_zfmisc_1(k1_tarski(esk3_1(esk2_0))))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32])]),c_0_30])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk1_0,X1)) != u1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_28])]),c_0_45])).

cnf(c_0_56,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = k6_domain_1(u1_struct_0(X1),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_44]),c_0_47]),c_0_48])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_1(esk2_0)),k1_tarski(esk3_1(esk2_0)))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( ~ v1_xboole_0(u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),X1) != u1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_28])]),c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_struct_0(esk2_0)
    | ~ r2_hidden(X1,k1_tarski(esk3_1(esk2_0)))
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_41])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_1(esk2_0),k1_tarski(esk3_1(esk2_0)))
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(esk2_0)
    | ~ r2_hidden(X2,k1_tarski(esk3_1(esk2_0)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | k1_tarski(X1) != u1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk3_1(esk2_0),u1_struct_0(X1))
    | ~ l1_struct_0(esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_67,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_27]),c_0_28])]),c_0_41])).

fof(c_0_70,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | l1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_71,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_27]),c_0_28])])).

cnf(c_0_73,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_28])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
