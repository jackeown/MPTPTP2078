%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1800+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:08 EST 2020

% Result     : Theorem 34.51s
% Output     : CNFRefutation 34.51s
% Verified   : 
% Statistics : Number of formulae       :   77 (1118 expanded)
%              Number of clauses        :   52 ( 388 expanded)
%              Number of leaves         :   12 ( 271 expanded)
%              Depth                    :   14
%              Number of atoms          :  296 (7008 expanded)
%              Number of equality atoms :   53 (1181 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT016+2.ax',abstractness_v1_pre_topc)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(t25_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X10700,X10701] :
      ( ( v1_pre_topc(k8_tmap_1(X10700,X10701))
        | v2_struct_0(X10700)
        | ~ v2_pre_topc(X10700)
        | ~ l1_pre_topc(X10700)
        | ~ m1_pre_topc(X10701,X10700) )
      & ( v2_pre_topc(k8_tmap_1(X10700,X10701))
        | v2_struct_0(X10700)
        | ~ v2_pre_topc(X10700)
        | ~ l1_pre_topc(X10700)
        | ~ m1_pre_topc(X10701,X10700) )
      & ( l1_pre_topc(k8_tmap_1(X10700,X10701))
        | v2_struct_0(X10700)
        | ~ v2_pre_topc(X10700)
        | ~ l1_pre_topc(X10700)
        | ~ m1_pre_topc(X10701,X10700) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1268_0)
    & v2_pre_topc(esk1268_0)
    & l1_pre_topc(esk1268_0)
    & ~ v2_struct_0(esk1269_0)
    & m1_pre_topc(esk1269_0,esk1268_0)
    & ( ~ v1_tsep_1(esk1269_0,esk1268_0)
      | ~ m1_pre_topc(esk1269_0,esk1268_0)
      | g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(esk1268_0)) != k8_tmap_1(esk1268_0,esk1269_0) )
    & ( v1_tsep_1(esk1269_0,esk1268_0)
      | g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(esk1268_0)) = k8_tmap_1(esk1268_0,esk1269_0) )
    & ( m1_pre_topc(esk1269_0,esk1268_0)
      | g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(esk1268_0)) = k8_tmap_1(esk1268_0,esk1269_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X5860] :
      ( ~ l1_pre_topc(X5860)
      | ~ v1_pre_topc(X5860)
      | X5860 = g1_pre_topc(u1_struct_0(X5860),u1_pre_topc(X5860)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_16,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk1269_0,esk1268_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1268_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1268_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1268_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X10933,X10934] :
      ( ~ l1_pre_topc(X10933)
      | ~ m1_pre_topc(X10934,X10933)
      | r1_tarski(u1_struct_0(X10934),u1_struct_0(X10933)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_22,plain,(
    ! [X10906] :
      ( ~ l1_pre_topc(X10906)
      | m1_pre_topc(X10906,X10906) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_23,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk1268_0,esk1269_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_25,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_26,plain,(
    ! [X10788,X10789,X10790] :
      ( ( u1_struct_0(k8_tmap_1(X10788,X10789)) = u1_struct_0(X10788)
        | v2_struct_0(X10789)
        | ~ m1_pre_topc(X10789,X10788)
        | v2_struct_0(X10788)
        | ~ v2_pre_topc(X10788)
        | ~ l1_pre_topc(X10788) )
      & ( ~ m1_subset_1(X10790,k1_zfmisc_1(u1_struct_0(X10788)))
        | X10790 != u1_struct_0(X10789)
        | u1_pre_topc(k8_tmap_1(X10788,X10789)) = k5_tmap_1(X10788,X10790)
        | v2_struct_0(X10789)
        | ~ m1_pre_topc(X10789,X10788)
        | v2_struct_0(X10788)
        | ~ v2_pre_topc(X10788)
        | ~ l1_pre_topc(X10788) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_27,plain,(
    ! [X10847,X10848] :
      ( ~ l1_pre_topc(X10847)
      | ~ m1_pre_topc(X10848,X10847)
      | m1_subset_1(u1_struct_0(X10848),k1_zfmisc_1(u1_struct_0(X10847))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_28,plain,(
    ! [X2019,X2020] :
      ( ( ~ m1_subset_1(X2019,k1_zfmisc_1(X2020))
        | r1_tarski(X2019,X2020) )
      & ( ~ r1_tarski(X2019,X2020)
        | m1_subset_1(X2019,k1_zfmisc_1(X2020)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_29,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X10884,X10885] :
      ( v2_struct_0(X10884)
      | ~ v2_pre_topc(X10884)
      | ~ l1_pre_topc(X10884)
      | v2_struct_0(X10885)
      | ~ m1_pre_topc(X10885,X10884)
      | k1_tsep_1(X10884,X10885,X10885) = g1_pre_topc(u1_struct_0(X10885),u1_pre_topc(X10885)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

cnf(c_0_31,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(esk1268_0,esk1269_0)),u1_pre_topc(k8_tmap_1(esk1268_0,esk1269_0))) = k8_tmap_1(esk1268_0,esk1269_0)
    | ~ v1_pre_topc(k8_tmap_1(esk1268_0,esk1269_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk1268_0,esk1269_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_34,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1269_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X10668,X10669] :
      ( v2_struct_0(X10668)
      | ~ v2_pre_topc(X10668)
      | ~ l1_pre_topc(X10668)
      | ~ m1_subset_1(X10669,k1_zfmisc_1(u1_struct_0(X10668)))
      | k6_tmap_1(X10668,X10669) = g1_pre_topc(u1_struct_0(X10668),k5_tmap_1(X10668,X10669)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1269_0),u1_struct_0(esk1268_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_19])])).

fof(c_0_41,plain,(
    ! [X10623,X10624,X10625] :
      ( ( ~ v1_tsep_1(X10624,X10623)
        | ~ m1_subset_1(X10625,k1_zfmisc_1(u1_struct_0(X10623)))
        | X10625 != u1_struct_0(X10624)
        | v3_pre_topc(X10625,X10623)
        | ~ m1_pre_topc(X10624,X10623)
        | ~ l1_pre_topc(X10623) )
      & ( m1_subset_1(esk1255_2(X10623,X10624),k1_zfmisc_1(u1_struct_0(X10623)))
        | v1_tsep_1(X10624,X10623)
        | ~ m1_pre_topc(X10624,X10623)
        | ~ l1_pre_topc(X10623) )
      & ( esk1255_2(X10623,X10624) = u1_struct_0(X10624)
        | v1_tsep_1(X10624,X10623)
        | ~ m1_pre_topc(X10624,X10623)
        | ~ l1_pre_topc(X10623) )
      & ( ~ v3_pre_topc(esk1255_2(X10623,X10624),X10623)
        | v1_tsep_1(X10624,X10623)
        | ~ m1_pre_topc(X10624,X10623)
        | ~ l1_pre_topc(X10623) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk1268_0,esk1268_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(esk1268_0,esk1269_0)),u1_pre_topc(k8_tmap_1(esk1268_0,esk1269_0))) = k8_tmap_1(esk1268_0,esk1269_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk1268_0,esk1269_0)) = u1_struct_0(esk1268_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19])]),c_0_35]),c_0_20])).

cnf(c_0_46,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk1269_0),k1_zfmisc_1(u1_struct_0(esk1268_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_tsep_1(esk1269_0,esk1268_0)
    | ~ m1_pre_topc(esk1269_0,esk1268_0)
    | g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(esk1268_0)) != k8_tmap_1(esk1268_0,esk1269_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v1_tsep_1(esk1269_0,esk1268_0)
    | g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(esk1268_0)) = k8_tmap_1(esk1268_0,esk1269_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(esk1268_0)) = k1_tsep_1(esk1268_0,esk1268_0,esk1268_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(k8_tmap_1(esk1268_0,esk1269_0))) = k8_tmap_1(esk1268_0,esk1269_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk1268_0,esk1269_0)) = k5_tmap_1(esk1268_0,u1_struct_0(esk1269_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk1268_0),k5_tmap_1(esk1268_0,u1_struct_0(esk1269_0))) = k6_tmap_1(esk1268_0,u1_struct_0(esk1269_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_56,plain,(
    ! [X10764,X10765] :
      ( ( ~ v3_pre_topc(X10765,X10764)
        | g1_pre_topc(u1_struct_0(X10764),u1_pre_topc(X10764)) = k6_tmap_1(X10764,X10765)
        | ~ m1_subset_1(X10765,k1_zfmisc_1(u1_struct_0(X10764)))
        | v2_struct_0(X10764)
        | ~ v2_pre_topc(X10764)
        | ~ l1_pre_topc(X10764) )
      & ( g1_pre_topc(u1_struct_0(X10764),u1_pre_topc(X10764)) != k6_tmap_1(X10764,X10765)
        | v3_pre_topc(X10765,X10764)
        | ~ m1_subset_1(X10765,k1_zfmisc_1(u1_struct_0(X10764)))
        | v2_struct_0(X10764)
        | ~ v2_pre_topc(X10764)
        | ~ l1_pre_topc(X10764) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

cnf(c_0_57,negated_conjecture,
    ( k8_tmap_1(esk1268_0,esk1269_0) != g1_pre_topc(u1_struct_0(esk1268_0),u1_pre_topc(esk1268_0))
    | ~ v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_17])])).

cnf(c_0_58,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( k8_tmap_1(esk1268_0,esk1269_0) = k1_tsep_1(esk1268_0,esk1268_0,esk1268_0)
    | v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k8_tmap_1(esk1268_0,esk1269_0) = k6_tmap_1(esk1268_0,u1_struct_0(esk1269_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_61,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k8_tmap_1(esk1268_0,esk1269_0) != k1_tsep_1(esk1268_0,esk1268_0,esk1268_0)
    | ~ v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk1269_0),esk1268_0)
    | ~ v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_17]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( k6_tmap_1(esk1268_0,u1_struct_0(esk1269_0)) = k1_tsep_1(esk1268_0,esk1268_0,esk1268_0)
    | v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k6_tmap_1(esk1268_0,u1_struct_0(esk1269_0)) = k1_tsep_1(esk1268_0,esk1268_0,esk1268_0)
    | ~ v3_pre_topc(u1_struct_0(esk1269_0),esk1268_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_48]),c_0_52]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_66,plain,
    ( esk1255_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_67,negated_conjecture,
    ( k6_tmap_1(esk1268_0,u1_struct_0(esk1269_0)) != k1_tsep_1(esk1268_0,esk1268_0,esk1268_0)
    | ~ v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k6_tmap_1(esk1268_0,u1_struct_0(esk1269_0)) = k1_tsep_1(esk1268_0,esk1268_0,esk1268_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk1255_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_70,negated_conjecture,
    ( esk1255_2(esk1268_0,esk1269_0) = u1_struct_0(esk1269_0)
    | v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_17]),c_0_19])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_tsep_1(esk1269_0,esk1268_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( v1_tsep_1(esk1269_0,esk1268_0)
    | ~ v3_pre_topc(esk1255_2(esk1268_0,esk1269_0),esk1268_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_17]),c_0_19])])).

cnf(c_0_73,negated_conjecture,
    ( esk1255_2(esk1268_0,esk1269_0) = u1_struct_0(esk1269_0) ),
    inference(sr,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_75,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk1269_0),esk1268_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_68]),c_0_52]),c_0_18]),c_0_19]),c_0_48])]),c_0_20]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
