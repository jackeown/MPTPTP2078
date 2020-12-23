%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:22 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  116 (2553 expanded)
%              Number of clauses        :   73 ( 958 expanded)
%              Number of leaves         :   21 ( 633 expanded)
%              Depth                    :   15
%              Number of atoms          :  364 (9443 expanded)
%              Number of equality atoms :   35 (1274 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v1_tdlat_3(X1) )
           => v1_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t58_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(d1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
      <=> u1_pre_topc(X1) = k9_setfam_1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t35_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v1_tops_2(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                   => ( X4 = X2
                     => v1_tops_2(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(t31_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

fof(t78_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v1_tdlat_3(X1) )
             => v1_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_tex_2])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | l1_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,plain,(
    ! [X28,X29] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)),X28)
        | ~ m1_pre_topc(X29,X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

fof(c_0_24,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | m1_pre_topc(X18,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & v1_tdlat_3(esk1_0)
    & ~ v1_tdlat_3(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | m1_pre_topc(X33,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_29,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
      | v2_pre_topc(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).

fof(c_0_30,plain,(
    ! [X40] :
      ( ~ l1_pre_topc(X40)
      | ~ v1_tdlat_3(X40)
      | v2_pre_topc(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

cnf(c_0_31,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X15] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_38,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_42,plain,(
    ! [X30,X31,X32] :
      ( ( ~ m1_pre_topc(X31,X30)
        | m1_pre_topc(X32,X30)
        | X31 != g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ l1_pre_topc(X30) )
      & ( ~ m1_pre_topc(X32,X30)
        | m1_pre_topc(X31,X30)
        | X31 != g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_44,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_33])])).

cnf(c_0_46,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

fof(c_0_48,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r1_tarski(u1_struct_0(X35),u1_struct_0(X36))
        | m1_pre_topc(X35,X36)
        | ~ m1_pre_topc(X36,X34)
        | ~ m1_pre_topc(X35,X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_pre_topc(X35,X36)
        | r1_tarski(u1_struct_0(X35),u1_struct_0(X36))
        | ~ m1_pre_topc(X36,X34)
        | ~ m1_pre_topc(X35,X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X37,X38,X39] :
      ( ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | ~ m1_pre_topc(X39,X38)
      | m1_pre_topc(X39,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_51,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_33])])).

cnf(c_0_54,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_40])])).

cnf(c_0_55,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_51,c_0_26])]),c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_33])]),c_0_54])])).

cnf(c_0_62,plain,
    ( m1_pre_topc(X1,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_40]),c_0_33])])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_61]),c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_60]),c_0_54]),c_0_33])])).

fof(c_0_67,plain,(
    ! [X41] :
      ( ( ~ v1_tdlat_3(X41)
        | u1_pre_topc(X41) = k9_setfam_1(u1_struct_0(X41))
        | ~ l1_pre_topc(X41) )
      & ( u1_pre_topc(X41) != k9_setfam_1(u1_struct_0(X41))
        | v1_tdlat_3(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tdlat_3])])])).

fof(c_0_68,plain,(
    ! [X11] : k9_setfam_1(X11) = k1_zfmisc_1(X11) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_69,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_70,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_54]),c_0_33])])).

cnf(c_0_73,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_60]),c_0_33])])).

cnf(c_0_74,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_66]),c_0_40])])).

cnf(c_0_75,plain,
    ( u1_pre_topc(X1) = k9_setfam_1(u1_struct_0(X1))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( v1_tdlat_3(X1)
    | u1_pre_topc(X1) != k9_setfam_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_78,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
      | ~ m1_pre_topc(X24,X22)
      | ~ v1_tops_2(X23,X22)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
      | X25 != X23
      | v1_tops_2(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).

fof(c_0_79,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
      | m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_73]),c_0_54]),c_0_33])])).

cnf(c_0_84,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_74]),c_0_40])])).

cnf(c_0_85,plain,
    ( u1_pre_topc(X1) = k1_zfmisc_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_87,plain,
    ( v1_tdlat_3(X1)
    | u1_pre_topc(X1) != k1_zfmisc_1(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_77,c_0_76])).

fof(c_0_88,plain,(
    ! [X26,X27] :
      ( ( ~ v1_tops_2(X27,X26)
        | r1_tarski(X27,u1_pre_topc(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_tarski(X27,u1_pre_topc(X26))
        | v1_tops_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).

cnf(c_0_89,plain,
    ( v1_tops_2(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_90,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_91,plain,
    ( r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_64])])).

cnf(c_0_93,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk1_0)) = u1_pre_topc(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_39]),c_0_40])])).

cnf(c_0_94,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk2_0)) != u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_33])])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_97,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]),c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_33])])).

cnf(c_0_99,negated_conjecture,
    ( u1_pre_topc(esk2_0) != u1_pre_topc(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_92]),c_0_93])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

fof(c_0_101,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_102,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_103,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_98]),c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk2_0))
    | ~ v1_tops_2(X1,esk2_0)
    | ~ r1_tarski(X1,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_92]),c_0_33]),c_0_93])])).

cnf(c_0_106,plain,
    ( v1_tops_2(X1,X2)
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_107,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_108,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( v1_tops_2(X1,esk2_0)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_pre_topc(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_92]),c_0_93])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_56])])).

cnf(c_0_111,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_93]),c_0_40])]),c_0_80])).

cnf(c_0_112,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_tops_2(u1_pre_topc(esk1_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_56]),c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_84]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.030 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t17_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v1_tdlat_3(X1))=>v1_tdlat_3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tex_2)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.13/0.39  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.13/0.39  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.39  fof(t58_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_pre_topc)).
% 0.13/0.39  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.13/0.39  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.13/0.39  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.13/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.39  fof(d1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)<=>u1_pre_topc(X1)=k9_setfam_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tdlat_3)).
% 0.13/0.39  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.13/0.39  fof(t35_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v1_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v1_tops_2(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 0.13/0.39  fof(t31_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 0.13/0.39  fof(t78_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>r1_tarski(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 0.13/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.39  fof(c_0_21, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v1_tdlat_3(X1))=>v1_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t17_tex_2])).
% 0.13/0.39  fof(c_0_22, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|l1_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_23, plain, ![X28, X29]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|~m1_pre_topc(X29,X28)|~l1_pre_topc(X28))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)),X28)|~m1_pre_topc(X29,X28)|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.13/0.39  fof(c_0_24, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|m1_pre_topc(X18,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.13/0.39  fof(c_0_25, negated_conjecture, (l1_pre_topc(esk1_0)&(l1_pre_topc(esk2_0)&((g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&v1_tdlat_3(esk1_0))&~v1_tdlat_3(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.13/0.39  cnf(c_0_26, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_27, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  fof(c_0_28, plain, ![X33]:(~l1_pre_topc(X33)|m1_pre_topc(X33,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.39  fof(c_0_29, plain, ![X16]:(~l1_pre_topc(X16)|(~v2_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|v2_pre_topc(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_pre_topc])])).
% 0.13/0.39  fof(c_0_30, plain, ![X40]:(~l1_pre_topc(X40)|(~v1_tdlat_3(X40)|v2_pre_topc(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.13/0.39  cnf(c_0_31, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_34, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_35, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_36, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  fof(c_0_37, plain, ![X15]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))|(~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15)))|(~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.13/0.39  cnf(c_0_38, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (v1_tdlat_3(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  fof(c_0_41, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  fof(c_0_42, plain, ![X30, X31, X32]:((~m1_pre_topc(X31,X30)|m1_pre_topc(X32,X30)|X31!=g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))|(~v2_pre_topc(X32)|~l1_pre_topc(X32))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))|~l1_pre_topc(X30))&(~m1_pre_topc(X32,X30)|m1_pre_topc(X31,X30)|X31!=g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))|(~v2_pre_topc(X32)|~l1_pre_topc(X32))|(~v2_pre_topc(X31)|~l1_pre_topc(X31))|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.39  cnf(c_0_44, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_33])])).
% 0.13/0.39  cnf(c_0_46, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.13/0.39  fof(c_0_48, plain, ![X34, X35, X36]:((~r1_tarski(u1_struct_0(X35),u1_struct_0(X36))|m1_pre_topc(X35,X36)|~m1_pre_topc(X36,X34)|~m1_pre_topc(X35,X34)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~m1_pre_topc(X35,X36)|r1_tarski(u1_struct_0(X35),u1_struct_0(X36))|~m1_pre_topc(X36,X34)|~m1_pre_topc(X35,X34)|(~v2_pre_topc(X34)|~l1_pre_topc(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.13/0.39  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  fof(c_0_50, plain, ![X37, X38, X39]:(~v2_pre_topc(X37)|~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|(~m1_pre_topc(X39,X38)|m1_pre_topc(X39,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.39  cnf(c_0_51, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_43, c_0_35])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_33])])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (v2_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_40])])).
% 0.13/0.39  cnf(c_0_55, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_57, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  cnf(c_0_58, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.39  cnf(c_0_59, plain, (m1_pre_topc(X1,X2)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_51, c_0_26])]), c_0_36])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_33])]), c_0_54])])).
% 0.13/0.39  cnf(c_0_62, plain, (m1_pre_topc(X1,X1)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  cnf(c_0_63, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~v2_pre_topc(X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_40]), c_0_33])])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (m1_pre_topc(esk2_0,X1)|~m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_32]), c_0_61]), c_0_33])])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_60]), c_0_54]), c_0_33])])).
% 0.13/0.39  fof(c_0_67, plain, ![X41]:((~v1_tdlat_3(X41)|u1_pre_topc(X41)=k9_setfam_1(u1_struct_0(X41))|~l1_pre_topc(X41))&(u1_pre_topc(X41)!=k9_setfam_1(u1_struct_0(X41))|v1_tdlat_3(X41)|~l1_pre_topc(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tdlat_3])])])).
% 0.13/0.39  fof(c_0_68, plain, ![X11]:k9_setfam_1(X11)=k1_zfmisc_1(X11), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.13/0.39  fof(c_0_69, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  fof(c_0_70, plain, ![X14]:(~l1_pre_topc(X14)|m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.13/0.39  cnf(c_0_71, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk1_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_54]), c_0_33])])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_60]), c_0_33])])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_66]), c_0_40])])).
% 0.13/0.39  cnf(c_0_75, plain, (u1_pre_topc(X1)=k9_setfam_1(u1_struct_0(X1))|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.39  cnf(c_0_76, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.13/0.39  cnf(c_0_77, plain, (v1_tdlat_3(X1)|u1_pre_topc(X1)!=k9_setfam_1(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.39  fof(c_0_78, plain, ![X22, X23, X24, X25]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|(~m1_pre_topc(X24,X22)|(~v1_tops_2(X23,X22)|(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|(X25!=X23|v1_tops_2(X25,X24))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).
% 0.13/0.39  fof(c_0_79, plain, ![X19, X20, X21]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).
% 0.13/0.39  cnf(c_0_80, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.13/0.39  cnf(c_0_81, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~r1_tarski(u1_struct_0(esk1_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_73]), c_0_54]), c_0_33])])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_74]), c_0_40])])).
% 0.13/0.39  cnf(c_0_85, plain, (u1_pre_topc(X1)=k1_zfmisc_1(u1_struct_0(X1))|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (~v1_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_87, plain, (v1_tdlat_3(X1)|u1_pre_topc(X1)!=k1_zfmisc_1(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(rw,[status(thm)],[c_0_77, c_0_76])).
% 0.13/0.39  fof(c_0_88, plain, ![X26, X27]:((~v1_tops_2(X27,X26)|r1_tarski(X27,u1_pre_topc(X26))|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~l1_pre_topc(X26))&(~r1_tarski(X27,u1_pre_topc(X26))|v1_tops_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).
% 0.13/0.39  cnf(c_0_89, plain, (v1_tops_2(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_pre_topc(X3,X1)|~v1_tops_2(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.13/0.39  cnf(c_0_90, plain, (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.13/0.39  cnf(c_0_91, plain, (r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.13/0.39  cnf(c_0_92, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_64])])).
% 0.13/0.39  cnf(c_0_93, negated_conjecture, (k1_zfmisc_1(u1_struct_0(esk1_0))=u1_pre_topc(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_39]), c_0_40])])).
% 0.13/0.39  cnf(c_0_94, negated_conjecture, (k1_zfmisc_1(u1_struct_0(esk2_0))!=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_33])])).
% 0.13/0.39  cnf(c_0_95, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v1_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.13/0.39  cnf(c_0_96, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.13/0.39  cnf(c_0_97, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]), c_0_90])).
% 0.13/0.39  cnf(c_0_98, negated_conjecture, (r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_33])])).
% 0.13/0.39  cnf(c_0_99, negated_conjecture, (u1_pre_topc(esk2_0)!=u1_pre_topc(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_92]), c_0_93])).
% 0.13/0.39  cnf(c_0_100, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v1_tops_2(X1,X2)|~l1_pre_topc(X2)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.13/0.39  fof(c_0_101, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.39  fof(c_0_102, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.39  cnf(c_0_103, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~r1_tarski(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_97, c_0_96])).
% 0.13/0.39  cnf(c_0_104, negated_conjecture, (~r1_tarski(u1_pre_topc(esk1_0),u1_pre_topc(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_98]), c_0_99])).
% 0.13/0.39  cnf(c_0_105, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk2_0))|~v1_tops_2(X1,esk2_0)|~r1_tarski(X1,u1_pre_topc(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_92]), c_0_33]), c_0_93])])).
% 0.13/0.39  cnf(c_0_106, plain, (v1_tops_2(X1,X2)|~r1_tarski(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.13/0.39  cnf(c_0_107, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.13/0.39  cnf(c_0_108, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.13/0.39  cnf(c_0_109, negated_conjecture, (v1_tops_2(X1,esk2_0)|~v1_tops_2(X1,X2)|~m1_pre_topc(esk2_0,X2)|~l1_pre_topc(X2)|~r1_tarski(X1,u1_pre_topc(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_92]), c_0_93])).
% 0.13/0.39  cnf(c_0_110, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_56])])).
% 0.13/0.39  cnf(c_0_111, negated_conjecture, (v1_tops_2(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_93]), c_0_40])]), c_0_80])).
% 0.13/0.39  cnf(c_0_112, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_107, c_0_108])).
% 0.13/0.39  cnf(c_0_113, negated_conjecture, (~v1_tops_2(u1_pre_topc(esk1_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_56]), c_0_110])).
% 0.13/0.39  cnf(c_0_114, negated_conjecture, (v1_tops_2(u1_pre_topc(esk1_0),esk1_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 0.13/0.39  cnf(c_0_115, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_84]), c_0_40])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 116
% 0.13/0.39  # Proof object clause steps            : 73
% 0.13/0.39  # Proof object formula steps           : 43
% 0.13/0.39  # Proof object conjectures             : 38
% 0.13/0.39  # Proof object clause conjectures      : 35
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 30
% 0.13/0.39  # Proof object initial formulas used   : 21
% 0.13/0.39  # Proof object generating inferences   : 34
% 0.13/0.39  # Proof object simplifying inferences  : 75
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 21
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 34
% 0.13/0.39  # Removed in clause preprocessing      : 2
% 0.13/0.39  # Initial clauses in saturation        : 32
% 0.13/0.39  # Processed clauses                    : 187
% 0.13/0.39  # ...of these trivial                  : 14
% 0.13/0.39  # ...subsumed                          : 22
% 0.13/0.39  # ...remaining for further processing  : 151
% 0.13/0.39  # Other redundant clauses eliminated   : 5
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 6
% 0.13/0.39  # Backward-rewritten                   : 14
% 0.13/0.39  # Generated clauses                    : 333
% 0.13/0.39  # ...of the previous two non-trivial   : 225
% 0.13/0.39  # Contextual simplify-reflections      : 9
% 0.13/0.39  # Paramodulations                      : 328
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 5
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 96
% 0.13/0.39  #    Positive orientable unit clauses  : 36
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 4
% 0.13/0.39  #    Non-unit-clauses                  : 56
% 0.13/0.39  # Current number of unprocessed clauses: 94
% 0.13/0.39  # ...number of literals in the above   : 310
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 52
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 838
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 372
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 34
% 0.13/0.39  # Unit Clause-clause subsumption calls : 106
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 33
% 0.13/0.39  # BW rewrite match successes           : 5
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 9637
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.002 s
% 0.13/0.39  # Total time               : 0.045 s
% 0.13/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
