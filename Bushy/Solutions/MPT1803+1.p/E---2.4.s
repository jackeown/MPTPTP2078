%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t119_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:04 EDT 2019

% Result     : Theorem 157.97s
% Output     : CNFRefutation 157.97s
% Verified   : 
% Statistics : Number of formulae       :  117 (2948 expanded)
%              Number of clauses        :   76 ( 940 expanded)
%              Number of leaves         :   20 ( 733 expanded)
%              Depth                    :   13
%              Number of atoms          :  598 (16578 expanded)
%              Number of equality atoms :   59 ( 434 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t119_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',t119_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',dt_m1_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',t1_tsep_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',t2_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',d11_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',dt_k6_tmap_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',t4_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',fc2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',t114_tmap_1)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',dt_k9_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',dt_k8_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',fc4_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',redefinition_k2_partfun1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',dt_k7_tmap_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',d4_tmap_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',t7_boole)).

fof(d12_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) )
             => ( X3 = k9_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',d12_tmap_1)).

fof(t110_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( u1_struct_0(X3) = X2
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',t110_tmap_1)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t119_tmap_1.p',redefinition_r1_funct_2)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t119_tmap_1])).

fof(c_0_21,plain,(
    ! [X80,X81] :
      ( ~ l1_pre_topc(X80)
      | ~ m1_pre_topc(X81,X80)
      | l1_pre_topc(X81) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ~ r1_tmap_1(esk2_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X155,X156] :
      ( ~ l1_pre_topc(X155)
      | ~ m1_pre_topc(X156,X155)
      | m1_subset_1(u1_struct_0(X156),k1_zfmisc_1(u1_struct_0(X155))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_24,plain,(
    ! [X158,X159] :
      ( ~ m1_subset_1(X158,X159)
      | v1_xboole_0(X159)
      | r2_hidden(X158,X159) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_25,plain,(
    ! [X79] :
      ( ~ l1_pre_topc(X79)
      | l1_struct_0(X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_26,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X25 != k8_tmap_1(X23,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | X26 != u1_struct_0(X24)
        | X25 = k6_tmap_1(X23,X26)
        | ~ v1_pre_topc(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk4_3(X23,X24,X25),k1_zfmisc_1(u1_struct_0(X23)))
        | X25 = k8_tmap_1(X23,X24)
        | ~ v1_pre_topc(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( esk4_3(X23,X24,X25) = u1_struct_0(X24)
        | X25 = k8_tmap_1(X23,X24)
        | ~ v1_pre_topc(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( X25 != k6_tmap_1(X23,esk4_3(X23,X24,X25))
        | X25 = k8_tmap_1(X23,X24)
        | ~ v1_pre_topc(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X24,X23)
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_30,plain,(
    ! [X62,X63] :
      ( ( v1_pre_topc(k6_tmap_1(X62,X63))
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62))) )
      & ( v2_pre_topc(k6_tmap_1(X62,X63))
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62))) )
      & ( l1_pre_topc(k6_tmap_1(X62,X63))
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(u1_struct_0(X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X173,X174,X175] :
      ( ~ r2_hidden(X173,X174)
      | ~ m1_subset_1(X174,k1_zfmisc_1(X175))
      | m1_subset_1(X173,X175) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_33,plain,(
    ! [X192] :
      ( v2_struct_0(X192)
      | ~ l1_struct_0(X192)
      | ~ v1_xboole_0(u1_struct_0(X192)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_38,plain,
    ( esk4_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28])])).

cnf(c_0_43,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_45,plain,(
    ! [X149,X150,X151] :
      ( ( u1_struct_0(k8_tmap_1(X149,X150)) = u1_struct_0(X149)
        | v2_struct_0(X150)
        | ~ m1_pre_topc(X150,X149)
        | v2_struct_0(X149)
        | ~ v2_pre_topc(X149)
        | ~ l1_pre_topc(X149) )
      & ( ~ m1_subset_1(X151,k1_zfmisc_1(u1_struct_0(X149)))
        | X151 != u1_struct_0(X150)
        | u1_pre_topc(k8_tmap_1(X149,X150)) = k5_tmap_1(X149,X151)
        | v2_struct_0(X150)
        | ~ m1_pre_topc(X150,X149)
        | v2_struct_0(X149)
        | ~ v2_pre_topc(X149)
        | ~ l1_pre_topc(X149) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( esk4_3(esk1_0,esk2_0,X1) = u1_struct_0(esk2_0)
    | X1 = k8_tmap_1(esk1_0,esk2_0)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_42]),c_0_28]),c_0_39])]),c_0_40])).

fof(c_0_55,plain,(
    ! [X77,X78] :
      ( ( v1_funct_1(k9_tmap_1(X77,X78))
        | v2_struct_0(X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77)
        | ~ m1_pre_topc(X78,X77) )
      & ( v1_funct_2(k9_tmap_1(X77,X78),u1_struct_0(X77),u1_struct_0(k8_tmap_1(X77,X78)))
        | v2_struct_0(X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77)
        | ~ m1_pre_topc(X78,X77) )
      & ( m1_subset_1(k9_tmap_1(X77,X78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X77),u1_struct_0(k8_tmap_1(X77,X78)))))
        | v2_struct_0(X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77)
        | ~ m1_pre_topc(X78,X77) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_56,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])]),c_0_50])).

fof(c_0_59,plain,(
    ! [X72,X73] :
      ( ( v1_pre_topc(k8_tmap_1(X72,X73))
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | ~ m1_pre_topc(X73,X72) )
      & ( v2_pre_topc(k8_tmap_1(X72,X73))
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | ~ m1_pre_topc(X73,X72) )
      & ( l1_pre_topc(k8_tmap_1(X72,X73))
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | ~ m1_pre_topc(X73,X72) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_60,plain,(
    ! [X193,X194] :
      ( ( ~ v2_struct_0(k6_tmap_1(X193,X194))
        | v2_struct_0(X193)
        | ~ v2_pre_topc(X193)
        | ~ l1_pre_topc(X193)
        | ~ m1_subset_1(X194,k1_zfmisc_1(u1_struct_0(X193))) )
      & ( v1_pre_topc(k6_tmap_1(X193,X194))
        | v2_struct_0(X193)
        | ~ v2_pre_topc(X193)
        | ~ l1_pre_topc(X193)
        | ~ m1_subset_1(X194,k1_zfmisc_1(u1_struct_0(X193))) )
      & ( v2_pre_topc(k6_tmap_1(X193,X194))
        | v2_struct_0(X193)
        | ~ v2_pre_topc(X193)
        | ~ l1_pre_topc(X193)
        | ~ m1_subset_1(X194,k1_zfmisc_1(u1_struct_0(X193))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_61,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk4_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( esk4_3(esk1_0,esk2_0,k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) = u1_struct_0(esk2_0)
    | k6_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k8_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

fof(c_0_63,plain,(
    ! [X108,X109,X110,X111] :
      ( ~ v1_funct_1(X110)
      | ~ m1_subset_1(X110,k1_zfmisc_1(k2_zfmisc_1(X108,X109)))
      | k2_partfun1(X108,X109,X110,X111) = k7_relat_1(X110,X111) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk1_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_27]),c_0_28]),c_0_39])]),c_0_40]),c_0_50])).

cnf(c_0_66,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_67,plain,(
    ! [X70,X71] :
      ( ( v1_funct_1(k7_tmap_1(X70,X71))
        | v2_struct_0(X70)
        | ~ v2_pre_topc(X70)
        | ~ l1_pre_topc(X70)
        | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70))) )
      & ( v1_funct_2(k7_tmap_1(X70,X71),u1_struct_0(X70),u1_struct_0(k6_tmap_1(X70,X71)))
        | v2_struct_0(X70)
        | ~ v2_pre_topc(X70)
        | ~ l1_pre_topc(X70)
        | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70))) )
      & ( m1_subset_1(k7_tmap_1(X70,X71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X70),u1_struct_0(k6_tmap_1(X70,X71)))))
        | v2_struct_0(X70)
        | ~ v2_pre_topc(X70)
        | ~ l1_pre_topc(X70)
        | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_69,plain,(
    ! [X33,X34,X35,X36] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
      | ~ m1_pre_topc(X36,X33)
      | k2_tmap_1(X33,X34,X35,X36) = k2_partfun1(u1_struct_0(X33),u1_struct_0(X34),X35,u1_struct_0(X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_70,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( k6_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k8_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_53]),c_0_27]),c_0_28]),c_0_54]),c_0_39]),c_0_52])]),c_0_40])).

cnf(c_0_74,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_75,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_28]),c_0_39])]),c_0_40]),c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_27]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_78,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_79,plain,(
    ! [X180,X181] :
      ( ~ r2_hidden(X180,X181)
      | ~ v1_xboole_0(X181) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

fof(c_0_82,plain,(
    ! [X28,X29,X30,X31] :
      ( ( X30 != k9_tmap_1(X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X28)))
        | X31 != u1_struct_0(X29)
        | r1_funct_2(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)),u1_struct_0(X28),u1_struct_0(k6_tmap_1(X28,X31)),X30,k7_tmap_1(X28,X31))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk5_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | X30 = k9_tmap_1(X28,X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( esk5_3(X28,X29,X30) = u1_struct_0(X29)
        | X30 = k9_tmap_1(X28,X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ r1_funct_2(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)),u1_struct_0(X28),u1_struct_0(k6_tmap_1(X28,esk5_3(X28,X29,X30))),X30,k7_tmap_1(X28,esk5_3(X28,X29,X30)))
        | X30 = k9_tmap_1(X28,X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_27]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_85,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_86,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_42]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_27]),c_0_28]),c_0_39])]),c_0_40]),c_0_65])).

cnf(c_0_88,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_tmap_1(esk1_0,esk2_0),X1) = k7_relat_1(k9_tmap_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

fof(c_0_89,plain,(
    ! [X145,X146,X147,X148] :
      ( v2_struct_0(X145)
      | ~ v2_pre_topc(X145)
      | ~ l1_pre_topc(X145)
      | ~ m1_subset_1(X146,k1_zfmisc_1(u1_struct_0(X145)))
      | v2_struct_0(X147)
      | ~ m1_pre_topc(X147,X145)
      | u1_struct_0(X147) != X146
      | ~ m1_subset_1(X148,u1_struct_0(X147))
      | r1_tmap_1(X147,k6_tmap_1(X145,X146),k2_tmap_1(X145,k6_tmap_1(X145,X146),k7_tmap_1(X145,X146),X147),X148) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).

fof(c_0_90,plain,(
    ! [X127,X128,X129,X130,X131,X132] :
      ( ( ~ r1_funct_2(X127,X128,X129,X130,X131,X132)
        | X131 = X132
        | v1_xboole_0(X128)
        | v1_xboole_0(X130)
        | ~ v1_funct_1(X131)
        | ~ v1_funct_2(X131,X127,X128)
        | ~ m1_subset_1(X131,k1_zfmisc_1(k2_zfmisc_1(X127,X128)))
        | ~ v1_funct_1(X132)
        | ~ v1_funct_2(X132,X129,X130)
        | ~ m1_subset_1(X132,k1_zfmisc_1(k2_zfmisc_1(X129,X130))) )
      & ( X131 != X132
        | r1_funct_2(X127,X128,X129,X130,X131,X132)
        | v1_xboole_0(X128)
        | v1_xboole_0(X130)
        | ~ v1_funct_1(X131)
        | ~ v1_funct_2(X131,X127,X128)
        | ~ m1_subset_1(X131,k1_zfmisc_1(k2_zfmisc_1(X127,X128)))
        | ~ v1_funct_1(X132)
        | ~ v1_funct_2(X132,X129,X130)
        | ~ m1_subset_1(X132,k1_zfmisc_1(k2_zfmisc_1(X129,X130))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_91,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),u1_struct_0(esk1_0),u1_struct_0(k6_tmap_1(esk1_0,u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_42]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_93,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_80]),c_0_81])]),c_0_40])).

cnf(c_0_96,plain,
    ( r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))
    | v2_struct_0(X2)
    | X1 != k9_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_97,negated_conjecture,
    ( k2_tmap_1(X1,k8_tmap_1(esk1_0,esk2_0),X2,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),X2,u1_struct_0(X3))
    | v2_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk1_0))))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_65]),c_0_84]),c_0_85])]),c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk1_0,k9_tmap_1(esk1_0,esk2_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_87]),c_0_77]),c_0_28]),c_0_39])]),c_0_40]),c_0_88]),c_0_76])])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_100,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_42]),c_0_28]),c_0_39])]),c_0_40]),c_0_73]),c_0_65])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_73]),c_0_65])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_42]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_104,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_105,plain,
    ( r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_96])]),c_0_31]),c_0_64]),c_0_66]),c_0_74])).

cnf(c_0_106,negated_conjecture,
    ( k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1) = k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_87]),c_0_88]),c_0_77]),c_0_76]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_107,negated_conjecture,
    ( k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk2_0)) = k2_tmap_1(esk1_0,esk1_0,k9_tmap_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_27])).

cnf(c_0_108,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X1)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_99]),c_0_31])).

cnf(c_0_109,negated_conjecture,
    ( X1 = k7_tmap_1(esk1_0,u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1,k7_tmap_1(esk1_0,u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_103])]),c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_27]),c_0_65]),c_0_73]),c_0_65]),c_0_28]),c_0_39])]),c_0_40])).

cnf(c_0_111,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_112,negated_conjecture,
    ( k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk2_0) = k2_tmap_1(esk1_0,esk1_0,k9_tmap_1(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_27]),c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk2_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_35]),c_0_50])).

cnf(c_0_114,negated_conjecture,
    ( k7_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k9_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_76]),c_0_110]),c_0_87]),c_0_77])]),c_0_104])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,esk1_0,k9_tmap_1(esk1_0,esk2_0),esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_27]),c_0_73]),c_0_73]),c_0_114]),c_0_112]),c_0_28]),c_0_39])]),c_0_115]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
