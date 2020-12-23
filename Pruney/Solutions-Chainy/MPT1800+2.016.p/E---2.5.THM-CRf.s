%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:24 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  117 (2226 expanded)
%              Number of clauses        :   86 ( 850 expanded)
%              Number of leaves         :   15 ( 550 expanded)
%              Depth                    :   18
%              Number of atoms          :  480 (12356 expanded)
%              Number of equality atoms :   57 (1680 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t116_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

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

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(d1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tsep_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r1_tarski(u1_struct_0(X34),u1_struct_0(X35))
        | m1_pre_topc(X34,X35)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ m1_pre_topc(X34,X35)
        | r1_tarski(u1_struct_0(X34),u1_struct_0(X35))
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_tmap_1])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ( ~ m1_pre_topc(X13,X14)
        | m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))
        | m1_pre_topc(X13,X14)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | m1_pre_topc(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)),X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ( ~ v1_tsep_1(esk4_0,esk3_0)
      | ~ m1_pre_topc(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) )
    & ( v1_tsep_1(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) )
    & ( m1_pre_topc(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).

fof(c_0_26,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | v2_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))
      | m1_pre_topc(X12,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_37,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_32]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_33]),c_0_34])])).

fof(c_0_42,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | m1_pre_topc(X30,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_43,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,plain,
    ( m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk4_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

fof(c_0_49,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | r1_tarski(u1_struct_0(X32),u1_struct_0(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_50,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X17 != k8_tmap_1(X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))
        | X18 != u1_struct_0(X16)
        | X17 = k6_tmap_1(X15,X18)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( esk1_3(X15,X16,X17) = u1_struct_0(X16)
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( X17 != k6_tmap_1(X15,esk1_3(X15,X16,X17))
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_51,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,X28)
      | m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_52,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33])])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40]),c_0_41])])).

cnf(c_0_55,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_40])])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_59,plain,(
    ! [X24,X25] :
      ( ( ~ v3_pre_topc(X25,X24)
        | g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)) = k6_tmap_1(X24,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)) != k6_tmap_1(X24,X25)
        | v3_pre_topc(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

cnf(c_0_60,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),esk3_0)
    | ~ l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_40])])).

cnf(c_0_65,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | v1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_44]),c_0_33])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_70,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | v2_pre_topc(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_63]),c_0_33]),c_0_34])])).

cnf(c_0_71,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_47]),c_0_56])])).

cnf(c_0_73,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_74,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_58]),c_0_28])).

fof(c_0_75,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v1_tsep_1(X21,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | X22 != u1_struct_0(X21)
        | v3_pre_topc(X22,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | v1_tsep_1(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( esk2_2(X20,X21) = u1_struct_0(X21)
        | v1_tsep_1(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ v3_pre_topc(esk2_2(X20,X21),X20)
        | v1_tsep_1(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_76,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k6_tmap_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_61])).

cnf(c_0_77,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk3_0,esk4_0)
    | v1_tsep_1(esk4_0,esk3_0)
    | ~ l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_32]),c_0_33]),c_0_34])]),c_0_69]),c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_44]),c_0_33])])).

cnf(c_0_79,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_72]),c_0_40]),c_0_41])])).

cnf(c_0_80,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | ~ m1_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_72]),c_0_40])])).

cnf(c_0_82,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk3_0)
    | v1_tsep_1(esk4_0,esk3_0)
    | k6_tmap_1(esk3_0,u1_struct_0(X1)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_44]),c_0_33]),c_0_34])]),c_0_69])).

cnf(c_0_85,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk3_0,esk4_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_79]),c_0_56]),c_0_40]),c_0_80])])).

cnf(c_0_87,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_37]),c_0_39]),c_0_40])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_89,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk4_0),esk3_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_32])])).

cnf(c_0_91,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_92,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_86]),c_0_56])])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_32])])).

cnf(c_0_95,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_32]),c_0_33])])).

cnf(c_0_96,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_97,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_91]),c_0_33]),c_0_34])]),c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_91]),c_0_33]),c_0_39])])).

cnf(c_0_99,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_100,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_61])).

cnf(c_0_101,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_39])).

cnf(c_0_102,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_103,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_104,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k6_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_98]),c_0_33]),c_0_34])]),c_0_69])).

cnf(c_0_105,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_47])).

cnf(c_0_106,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(X1)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_33]),c_0_34])]),c_0_69])).

cnf(c_0_107,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_55]),c_0_56]),c_0_40])])).

cnf(c_0_108,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_109,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_104]),c_0_33])])).

cnf(c_0_110,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_104]),c_0_33]),c_0_34])])).

cnf(c_0_111,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_104]),c_0_33])])).

cnf(c_0_112,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_87]),c_0_107])])).

cnf(c_0_113,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_114,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_32]),c_0_33]),c_0_34])]),c_0_69]),c_0_110]),c_0_111]),c_0_112])).

cnf(c_0_115,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_113]),c_0_61])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_95]),c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.17/3.34  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 3.17/3.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.17/3.34  #
% 3.17/3.34  # Preprocessing time       : 0.029 s
% 3.17/3.34  
% 3.17/3.34  # Proof found!
% 3.17/3.34  # SZS status Theorem
% 3.17/3.34  # SZS output start CNFRefutation
% 3.17/3.34  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/3.34  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.17/3.34  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 3.17/3.34  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.17/3.34  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.17/3.34  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 3.17/3.34  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 3.17/3.34  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.17/3.34  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.17/3.34  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.17/3.34  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.17/3.34  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 3.17/3.34  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.17/3.34  fof(t106_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.17/3.34  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 3.17/3.34  fof(c_0_15, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.17/3.34  fof(c_0_16, plain, ![X33, X34, X35]:((~r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|m1_pre_topc(X34,X35)|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~m1_pre_topc(X34,X35)|r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 3.17/3.34  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.17/3.34  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 3.17/3.34  fof(c_0_19, plain, ![X13, X14]:((~m1_pre_topc(X13,X14)|m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(~m1_pre_topc(X13,g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)))|m1_pre_topc(X13,X14)|~l1_pre_topc(X14)|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 3.17/3.34  fof(c_0_20, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 3.17/3.34  fof(c_0_21, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_pre_topc(X38,X37)|m1_pre_topc(X38,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 3.17/3.34  fof(c_0_22, plain, ![X26, X27]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)),X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 3.17/3.34  cnf(c_0_23, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.17/3.34  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 3.17/3.34  fof(c_0_25, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0))&((v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0))&(m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).
% 3.17/3.34  fof(c_0_26, plain, ![X7, X8]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|v2_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 3.17/3.34  cnf(c_0_27, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.17/3.34  cnf(c_0_28, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.17/3.34  cnf(c_0_29, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.17/3.34  cnf(c_0_30, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.17/3.34  cnf(c_0_31, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 3.17/3.34  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.17/3.34  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.17/3.34  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.17/3.34  cnf(c_0_35, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.17/3.34  fof(c_0_36, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)))|m1_pre_topc(X12,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 3.17/3.34  cnf(c_0_37, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 3.17/3.34  cnf(c_0_38, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_28])).
% 3.17/3.34  cnf(c_0_39, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 3.17/3.34  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_32]), c_0_33])])).
% 3.17/3.34  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_33]), c_0_34])])).
% 3.17/3.34  fof(c_0_42, plain, ![X30]:(~l1_pre_topc(X30)|m1_pre_topc(X30,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 3.17/3.34  cnf(c_0_43, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.17/3.34  cnf(c_0_44, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.17/3.34  cnf(c_0_45, plain, (m1_pre_topc(X1,X2)|~m1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_29, c_0_37])).
% 3.17/3.34  cnf(c_0_46, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk4_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 3.17/3.34  cnf(c_0_47, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.17/3.34  cnf(c_0_48, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 3.17/3.34  fof(c_0_49, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|r1_tarski(u1_struct_0(X32),u1_struct_0(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 3.17/3.34  fof(c_0_50, plain, ![X15, X16, X17, X18]:((X17!=k8_tmap_1(X15,X16)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))|(X18!=u1_struct_0(X16)|X17=k6_tmap_1(X15,X18)))|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((esk1_3(X15,X16,X17)=u1_struct_0(X16)|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(X17!=k6_tmap_1(X15,esk1_3(X15,X16,X17))|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 3.17/3.34  fof(c_0_51, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_pre_topc(X29,X28)|m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 3.17/3.34  cnf(c_0_52, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.17/3.34  cnf(c_0_53, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_33])])).
% 3.17/3.34  cnf(c_0_54, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_40]), c_0_41])])).
% 3.17/3.34  cnf(c_0_55, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_47])).
% 3.17/3.34  cnf(c_0_56, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_39]), c_0_40])])).
% 3.17/3.34  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.17/3.34  cnf(c_0_58, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 3.17/3.34  fof(c_0_59, plain, ![X24, X25]:((~v3_pre_topc(X25,X24)|g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))=k6_tmap_1(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))!=k6_tmap_1(X24,X25)|v3_pre_topc(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).
% 3.17/3.34  cnf(c_0_60, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 3.17/3.34  cnf(c_0_61, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.17/3.34  cnf(c_0_62, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 3.17/3.34  cnf(c_0_63, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),esk3_0)|~l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_47])).
% 3.17/3.34  cnf(c_0_64, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_40])])).
% 3.17/3.34  cnf(c_0_65, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 3.17/3.34  cnf(c_0_66, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=k6_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 3.17/3.34  cnf(c_0_67, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(k8_tmap_1(X1,X2))|~m1_pre_topc(X2,X1)|~l1_pre_topc(k8_tmap_1(X1,X2))|~l1_pre_topc(X1)|~v2_pre_topc(k8_tmap_1(X1,X2))|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])]), c_0_61])).
% 3.17/3.34  cnf(c_0_68, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|v1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_44]), c_0_33])])).
% 3.17/3.34  cnf(c_0_69, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.17/3.34  cnf(c_0_70, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|v2_pre_topc(k8_tmap_1(esk3_0,esk4_0))|~l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_63]), c_0_33]), c_0_34])])).
% 3.17/3.34  cnf(c_0_71, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 3.17/3.34  cnf(c_0_72, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_47]), c_0_56])])).
% 3.17/3.34  cnf(c_0_73, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 3.17/3.34  cnf(c_0_74, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_58]), c_0_28])).
% 3.17/3.34  fof(c_0_75, plain, ![X20, X21, X22]:((~v1_tsep_1(X21,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(X22!=u1_struct_0(X21)|v3_pre_topc(X22,X20)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|v1_tsep_1(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&((esk2_2(X20,X21)=u1_struct_0(X21)|v1_tsep_1(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))&(~v3_pre_topc(esk2_2(X20,X21),X20)|v1_tsep_1(X21,X20)|~m1_pre_topc(X21,X20)|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 3.17/3.34  cnf(c_0_76, plain, (v3_pre_topc(u1_struct_0(X1),X2)|v2_struct_0(X2)|g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))!=k6_tmap_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_66, c_0_61])).
% 3.17/3.34  cnf(c_0_77, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))=k8_tmap_1(esk3_0,esk4_0)|v1_tsep_1(esk4_0,esk3_0)|~l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_32]), c_0_33]), c_0_34])]), c_0_69]), c_0_70])).
% 3.17/3.34  cnf(c_0_78, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_44]), c_0_33])])).
% 3.17/3.34  cnf(c_0_79, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_72]), c_0_40]), c_0_41])])).
% 3.17/3.34  cnf(c_0_80, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_39]), c_0_40]), c_0_41])])).
% 3.17/3.34  cnf(c_0_81, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|~m1_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_72]), c_0_40])])).
% 3.17/3.34  cnf(c_0_82, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 3.17/3.34  cnf(c_0_83, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 3.17/3.34  cnf(c_0_84, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk3_0)|v1_tsep_1(esk4_0,esk3_0)|k6_tmap_1(esk3_0,u1_struct_0(X1))!=k8_tmap_1(esk3_0,esk4_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_44]), c_0_33]), c_0_34])]), c_0_69])).
% 3.17/3.34  cnf(c_0_85, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))=k8_tmap_1(esk3_0,esk4_0)|v1_tsep_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 3.17/3.34  cnf(c_0_86, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_79]), c_0_56]), c_0_40]), c_0_80])])).
% 3.17/3.34  cnf(c_0_87, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_37]), c_0_39]), c_0_40])])).
% 3.17/3.34  cnf(c_0_88, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.17/3.34  cnf(c_0_89, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 3.17/3.34  cnf(c_0_90, negated_conjecture, (v3_pre_topc(u1_struct_0(esk4_0),esk3_0)|v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_32])])).
% 3.17/3.34  cnf(c_0_91, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_32]), c_0_33]), c_0_34])])).
% 3.17/3.34  cnf(c_0_92, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_86]), c_0_56])])).
% 3.17/3.34  cnf(c_0_93, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_61, c_0_87])).
% 3.17/3.34  cnf(c_0_94, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_32])])).
% 3.17/3.34  cnf(c_0_95, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_32]), c_0_33])])).
% 3.17/3.34  cnf(c_0_96, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=k6_tmap_1(X2,X1)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 3.17/3.34  cnf(c_0_97, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(X1,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_91]), c_0_33]), c_0_34])]), c_0_92])).
% 3.17/3.34  cnf(c_0_98, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_91]), c_0_33]), c_0_39])])).
% 3.17/3.34  cnf(c_0_99, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 3.17/3.34  cnf(c_0_100, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_96, c_0_61])).
% 3.17/3.34  cnf(c_0_101, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_97, c_0_39])).
% 3.17/3.34  cnf(c_0_102, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|X1!=k6_tmap_1(X2,esk1_3(X2,X3,X1))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 3.17/3.34  cnf(c_0_103, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 3.17/3.34  cnf(c_0_104, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k6_tmap_1(esk3_0,u1_struct_0(esk4_0))|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_98]), c_0_33]), c_0_34])]), c_0_69])).
% 3.17/3.34  cnf(c_0_105, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_73, c_0_47])).
% 3.17/3.34  cnf(c_0_106, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(X1))!=k8_tmap_1(esk3_0,esk4_0)|~v3_pre_topc(u1_struct_0(X1),esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_33]), c_0_34])]), c_0_69])).
% 3.17/3.34  cnf(c_0_107, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_55]), c_0_56]), c_0_40])])).
% 3.17/3.34  cnf(c_0_108, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~l1_pre_topc(X1)|~v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~v2_pre_topc(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103])])).
% 3.17/3.34  cnf(c_0_109, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_104]), c_0_33])])).
% 3.17/3.34  cnf(c_0_110, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_104]), c_0_33]), c_0_34])])).
% 3.17/3.34  cnf(c_0_111, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_104]), c_0_33])])).
% 3.17/3.34  cnf(c_0_112, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))!=k8_tmap_1(esk3_0,esk4_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_87]), c_0_107])])).
% 3.17/3.34  cnf(c_0_113, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 3.17/3.34  cnf(c_0_114, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_32]), c_0_33]), c_0_34])]), c_0_69]), c_0_110]), c_0_111]), c_0_112])).
% 3.17/3.34  cnf(c_0_115, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_113]), c_0_61])).
% 3.17/3.34  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_95]), c_0_32]), c_0_33])]), ['proof']).
% 3.17/3.34  # SZS output end CNFRefutation
% 3.17/3.34  # Proof object total steps             : 117
% 3.17/3.34  # Proof object clause steps            : 86
% 3.17/3.34  # Proof object formula steps           : 31
% 3.17/3.34  # Proof object conjectures             : 49
% 3.17/3.34  # Proof object clause conjectures      : 46
% 3.17/3.34  # Proof object formula conjectures     : 3
% 3.17/3.34  # Proof object initial clauses used    : 27
% 3.17/3.34  # Proof object initial formulas used   : 15
% 3.17/3.34  # Proof object generating inferences   : 53
% 3.17/3.34  # Proof object simplifying inferences  : 118
% 3.17/3.34  # Training examples: 0 positive, 0 negative
% 3.17/3.34  # Parsed axioms                        : 15
% 3.17/3.34  # Removed by relevancy pruning/SinE    : 0
% 3.17/3.34  # Initial clauses                      : 34
% 3.17/3.34  # Removed in clause preprocessing      : 0
% 3.17/3.34  # Initial clauses in saturation        : 34
% 3.17/3.34  # Processed clauses                    : 22435
% 3.17/3.34  # ...of these trivial                  : 287
% 3.17/3.34  # ...subsumed                          : 19304
% 3.17/3.34  # ...remaining for further processing  : 2844
% 3.17/3.34  # Other redundant clauses eliminated   : 17
% 3.17/3.34  # Clauses deleted for lack of memory   : 0
% 3.17/3.34  # Backward-subsumed                    : 223
% 3.17/3.34  # Backward-rewritten                   : 77
% 3.17/3.34  # Generated clauses                    : 234050
% 3.17/3.34  # ...of the previous two non-trivial   : 211362
% 3.17/3.34  # Contextual simplify-reflections      : 784
% 3.17/3.34  # Paramodulations                      : 234025
% 3.17/3.34  # Factorizations                       : 0
% 3.17/3.34  # Equation resolutions                 : 26
% 3.17/3.34  # Propositional unsat checks           : 0
% 3.17/3.34  #    Propositional check models        : 0
% 3.17/3.34  #    Propositional check unsatisfiable : 0
% 3.17/3.34  #    Propositional clauses             : 0
% 3.17/3.34  #    Propositional clauses after purity: 0
% 3.17/3.34  #    Propositional unsat core size     : 0
% 3.17/3.34  #    Propositional preprocessing time  : 0.000
% 3.17/3.34  #    Propositional encoding time       : 0.000
% 3.17/3.34  #    Propositional solver time         : 0.000
% 3.17/3.34  #    Success case prop preproc time    : 0.000
% 3.17/3.34  #    Success case prop encoding time   : 0.000
% 3.17/3.34  #    Success case prop solver time     : 0.000
% 3.17/3.34  # Current number of processed clauses  : 2540
% 3.17/3.34  #    Positive orientable unit clauses  : 83
% 3.17/3.34  #    Positive unorientable unit clauses: 0
% 3.17/3.34  #    Negative unit clauses             : 4
% 3.17/3.34  #    Non-unit-clauses                  : 2453
% 3.17/3.34  # Current number of unprocessed clauses: 187939
% 3.17/3.34  # ...number of literals in the above   : 1028915
% 3.17/3.34  # Current number of archived formulas  : 0
% 3.17/3.34  # Current number of archived clauses   : 300
% 3.17/3.34  # Clause-clause subsumption calls (NU) : 1158449
% 3.17/3.34  # Rec. Clause-clause subsumption calls : 391949
% 3.17/3.34  # Non-unit clause-clause subsumptions  : 20283
% 3.17/3.34  # Unit Clause-clause subsumption calls : 1464
% 3.17/3.34  # Rewrite failures with RHS unbound    : 0
% 3.17/3.34  # BW rewrite match attempts            : 1700
% 3.17/3.34  # BW rewrite match successes           : 19
% 3.17/3.34  # Condensation attempts                : 0
% 3.17/3.34  # Condensation successes               : 0
% 3.17/3.34  # Termbank termtop insertions          : 9199772
% 3.17/3.35  
% 3.17/3.35  # -------------------------------------------------
% 3.17/3.35  # User time                : 2.917 s
% 3.17/3.35  # System time              : 0.097 s
% 3.17/3.35  # Total time               : 3.014 s
% 3.17/3.35  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
