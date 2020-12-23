%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t118_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:04 EDT 2019

% Result     : Theorem 208.81s
% Output     : CNFRefutation 208.81s
% Verified   : 
% Statistics : Number of formulae       :  146 (4922 expanded)
%              Number of clauses        :  101 (1584 expanded)
%              Number of leaves         :   22 (1221 expanded)
%              Depth                    :   14
%              Number of atoms          :  655 (35556 expanded)
%              Number of equality atoms :   63 ( 705 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t118_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t118_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_m1_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t1_tsep_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t2_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d11_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k6_tmap_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t4_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',fc2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t114_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',symmetry_r1_tsep_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k7_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k8_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',fc4_tmap_1)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',dt_k9_tmap_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d3_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d4_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',redefinition_k2_partfun1)).

fof(t109_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t109_tmap_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',t7_boole)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',d12_tmap_1)).

fof(reflexivity_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => r1_funct_2(X1,X2,X3,X4,X5,X5) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t118_tmap_1.p',reflexivity_r1_funct_2)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_tsep_1(X2,X3)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X3))
                     => r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t118_tmap_1])).

fof(c_0_23,plain,(
    ! [X83,X84] :
      ( ~ l1_pre_topc(X83)
      | ~ m1_pre_topc(X84,X83)
      | l1_pre_topc(X84) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & r1_tsep_1(esk2_0,esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ~ r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_25,plain,(
    ! [X162,X163] :
      ( ~ l1_pre_topc(X162)
      | ~ m1_pre_topc(X163,X162)
      | m1_subset_1(u1_struct_0(X163),k1_zfmisc_1(u1_struct_0(X162))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_26,plain,(
    ! [X165,X166] :
      ( ~ m1_subset_1(X165,X166)
      | v1_xboole_0(X166)
      | r2_hidden(X165,X166) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_27,plain,(
    ! [X82] :
      ( ~ l1_pre_topc(X82)
      | l1_struct_0(X82) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X24,X25,X26,X27] :
      ( ( X26 != k8_tmap_1(X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | X27 != u1_struct_0(X25)
        | X26 = k6_tmap_1(X24,X27)
        | ~ v1_pre_topc(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk5_3(X24,X25,X26),k1_zfmisc_1(u1_struct_0(X24)))
        | X26 = k8_tmap_1(X24,X25)
        | ~ v1_pre_topc(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( esk5_3(X24,X25,X26) = u1_struct_0(X25)
        | X26 = k8_tmap_1(X24,X25)
        | ~ v1_pre_topc(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( X26 != k6_tmap_1(X24,esk5_3(X24,X25,X26))
        | X26 = k8_tmap_1(X24,X25)
        | ~ v1_pre_topc(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_32,plain,(
    ! [X65,X66] :
      ( ( v1_pre_topc(k6_tmap_1(X65,X66))
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65))) )
      & ( v2_pre_topc(k6_tmap_1(X65,X66))
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65))) )
      & ( l1_pre_topc(k6_tmap_1(X65,X66))
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X180,X181,X182] :
      ( ~ r2_hidden(X180,X181)
      | ~ m1_subset_1(X181,k1_zfmisc_1(X182))
      | m1_subset_1(X180,X182) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_36,plain,(
    ! [X199] :
      ( v2_struct_0(X199)
      | ~ l1_struct_0(X199)
      | ~ v1_xboole_0(u1_struct_0(X199)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_41,plain,
    ( esk5_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])])).

cnf(c_0_46,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_30])])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( esk5_3(esk1_0,esk2_0,X1) = u1_struct_0(esk2_0)
    | X1 = k8_tmap_1(esk1_0,esk2_0)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_34]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_30]),c_0_42])]),c_0_43])).

fof(c_0_58,plain,(
    ! [X156,X157,X158] :
      ( ( u1_struct_0(k8_tmap_1(X156,X157)) = u1_struct_0(X156)
        | v2_struct_0(X157)
        | ~ m1_pre_topc(X157,X156)
        | v2_struct_0(X156)
        | ~ v2_pre_topc(X156)
        | ~ l1_pre_topc(X156) )
      & ( ~ m1_subset_1(X158,k1_zfmisc_1(u1_struct_0(X156)))
        | X158 != u1_struct_0(X157)
        | u1_pre_topc(k8_tmap_1(X156,X157)) = k5_tmap_1(X156,X158)
        | v2_struct_0(X157)
        | ~ m1_pre_topc(X157,X156)
        | v2_struct_0(X156)
        | ~ v2_pre_topc(X156)
        | ~ l1_pre_topc(X156) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_59,plain,(
    ! [X148,X149] :
      ( ~ l1_struct_0(X148)
      | ~ l1_struct_0(X149)
      | ~ r1_tsep_1(X148,X149)
      | r1_tsep_1(X149,X148) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_30])])).

fof(c_0_61,plain,(
    ! [X73,X74] :
      ( ( v1_funct_1(k7_tmap_1(X73,X74))
        | v2_struct_0(X73)
        | ~ v2_pre_topc(X73)
        | ~ l1_pre_topc(X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73))) )
      & ( v1_funct_2(k7_tmap_1(X73,X74),u1_struct_0(X73),u1_struct_0(k6_tmap_1(X73,X74)))
        | v2_struct_0(X73)
        | ~ v2_pre_topc(X73)
        | ~ l1_pre_topc(X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73))) )
      & ( m1_subset_1(k7_tmap_1(X73,X74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X73),u1_struct_0(k6_tmap_1(X73,X74)))))
        | v2_struct_0(X73)
        | ~ v2_pre_topc(X73)
        | ~ l1_pre_topc(X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(u1_struct_0(X73))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),c_0_53])).

fof(c_0_64,plain,(
    ! [X75,X76] :
      ( ( v1_pre_topc(k8_tmap_1(X75,X76))
        | v2_struct_0(X75)
        | ~ v2_pre_topc(X75)
        | ~ l1_pre_topc(X75)
        | ~ m1_pre_topc(X76,X75) )
      & ( v2_pre_topc(k8_tmap_1(X75,X76))
        | v2_struct_0(X75)
        | ~ v2_pre_topc(X75)
        | ~ l1_pre_topc(X75)
        | ~ m1_pre_topc(X76,X75) )
      & ( l1_pre_topc(k8_tmap_1(X75,X76))
        | v2_struct_0(X75)
        | ~ v2_pre_topc(X75)
        | ~ l1_pre_topc(X75)
        | ~ m1_pre_topc(X76,X75) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_65,plain,(
    ! [X200,X201] :
      ( ( ~ v2_struct_0(k6_tmap_1(X200,X201))
        | v2_struct_0(X200)
        | ~ v2_pre_topc(X200)
        | ~ l1_pre_topc(X200)
        | ~ m1_subset_1(X201,k1_zfmisc_1(u1_struct_0(X200))) )
      & ( v1_pre_topc(k6_tmap_1(X200,X201))
        | v2_struct_0(X200)
        | ~ v2_pre_topc(X200)
        | ~ l1_pre_topc(X200)
        | ~ m1_subset_1(X201,k1_zfmisc_1(u1_struct_0(X200))) )
      & ( v2_pre_topc(k6_tmap_1(X200,X201))
        | v2_struct_0(X200)
        | ~ v2_pre_topc(X200)
        | ~ l1_pre_topc(X200)
        | ~ m1_subset_1(X201,k1_zfmisc_1(u1_struct_0(X200))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_66,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk5_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( esk5_3(esk1_0,esk2_0,k6_tmap_1(esk1_0,u1_struct_0(esk2_0))) = u1_struct_0(esk2_0)
    | k6_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k8_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])])).

fof(c_0_68,plain,(
    ! [X80,X81] :
      ( ( v1_funct_1(k9_tmap_1(X80,X81))
        | v2_struct_0(X80)
        | ~ v2_pre_topc(X80)
        | ~ l1_pre_topc(X80)
        | ~ m1_pre_topc(X81,X80) )
      & ( v1_funct_2(k9_tmap_1(X80,X81),u1_struct_0(X80),u1_struct_0(k8_tmap_1(X80,X81)))
        | v2_struct_0(X80)
        | ~ v2_pre_topc(X80)
        | ~ l1_pre_topc(X80)
        | ~ m1_pre_topc(X81,X80) )
      & ( m1_subset_1(k9_tmap_1(X80,X81),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X80),u1_struct_0(k8_tmap_1(X80,X81)))))
        | v2_struct_0(X80)
        | ~ v2_pre_topc(X80)
        | ~ l1_pre_topc(X80)
        | ~ m1_pre_topc(X81,X80) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_69,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_71,plain,(
    ! [X34,X35] :
      ( ( ~ r1_tsep_1(X34,X35)
        | r1_xboole_0(u1_struct_0(X34),u1_struct_0(X35))
        | ~ l1_struct_0(X35)
        | ~ l1_struct_0(X34) )
      & ( ~ r1_xboole_0(u1_struct_0(X34),u1_struct_0(X35))
        | r1_tsep_1(X34,X35)
        | ~ l1_struct_0(X35)
        | ~ l1_struct_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_72,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_74,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_60])).

cnf(c_0_75,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_77,plain,(
    ! [X36,X37,X38,X39] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
      | ~ m1_pre_topc(X39,X36)
      | k2_tmap_1(X36,X37,X38,X39) = k2_partfun1(u1_struct_0(X36),u1_struct_0(X37),X38,u1_struct_0(X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_78,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_79,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( k6_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k8_tmap_1(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_56]),c_0_34]),c_0_30]),c_0_57]),c_0_42]),c_0_55])]),c_0_43])).

fof(c_0_82,plain,(
    ! [X111,X112,X113,X114] :
      ( ~ v1_funct_1(X113)
      | ~ m1_subset_1(X113,k1_zfmisc_1(k2_zfmisc_1(X111,X112)))
      | k2_partfun1(X111,X112,X113,X114) = k7_relat_1(X113,X114) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_83,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk1_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_34]),c_0_30]),c_0_42])]),c_0_43]),c_0_70])).

cnf(c_0_85,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_86,plain,(
    ! [X152,X153,X154,X155] :
      ( v2_struct_0(X152)
      | ~ v2_pre_topc(X152)
      | ~ l1_pre_topc(X152)
      | ~ m1_subset_1(X153,k1_zfmisc_1(u1_struct_0(X152)))
      | v2_struct_0(X154)
      | ~ m1_pre_topc(X154,X152)
      | ~ r1_xboole_0(u1_struct_0(X154),X153)
      | ~ m1_subset_1(X155,u1_struct_0(X154))
      | r1_tmap_1(X154,k6_tmap_1(X152,X153),k2_tmap_1(X152,k6_tmap_1(X152,X153),k7_tmap_1(X152,X153),X154),X155) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).

cnf(c_0_87,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_52]),c_0_74])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),u1_struct_0(esk1_0),u1_struct_0(k6_tmap_1(esk1_0,u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_45]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_90,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_91,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_92,plain,(
    ! [X187,X188] :
      ( ~ r2_hidden(X187,X188)
      | ~ v1_xboole_0(X188) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk4_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_76])).

cnf(c_0_94,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_95,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_34]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_97,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_34]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_98,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_45]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_99,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_100,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_34]),c_0_30]),c_0_42])]),c_0_43]),c_0_84])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_34]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_103,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_104,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_74]),c_0_52])])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_81]),c_0_84])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_45]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_45]),c_0_30]),c_0_42])]),c_0_43]),c_0_81]),c_0_84])).

fof(c_0_108,plain,(
    ! [X29,X30,X31,X32] :
      ( ( X31 != k9_tmap_1(X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X29)))
        | X32 != u1_struct_0(X30)
        | r1_funct_2(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)),u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,X32)),X31,k7_tmap_1(X29,X32))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))))
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk6_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))
        | X31 = k9_tmap_1(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))))
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( esk6_3(X29,X30,X31) = u1_struct_0(X30)
        | X31 = k9_tmap_1(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))))
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ r1_funct_2(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)),u1_struct_0(X29),u1_struct_0(k6_tmap_1(X29,esk6_3(X29,X30,X31))),X31,k7_tmap_1(X29,esk6_3(X29,X30,X31)))
        | X31 = k9_tmap_1(X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))))
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

fof(c_0_109,plain,(
    ! [X136,X137,X138,X139,X140,X141] :
      ( v1_xboole_0(X137)
      | v1_xboole_0(X139)
      | ~ v1_funct_1(X140)
      | ~ v1_funct_2(X140,X136,X137)
      | ~ m1_subset_1(X140,k1_zfmisc_1(k2_zfmisc_1(X136,X137)))
      | ~ v1_funct_1(X141)
      | ~ v1_funct_2(X141,X138,X139)
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(X138,X139)))
      | r1_funct_2(X136,X137,X138,X139,X140,X140) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).

cnf(c_0_110,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk1_0,esk3_0)) = u1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_29]),c_0_30]),c_0_42])]),c_0_43]),c_0_53])).

cnf(c_0_111,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_93]),c_0_94])]),c_0_43])).

cnf(c_0_113,negated_conjecture,
    ( k2_tmap_1(X1,k8_tmap_1(esk1_0,esk2_0),X2,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(esk1_0),X2,u1_struct_0(X3))
    | v2_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk1_0))))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_84]),c_0_96]),c_0_97])]),c_0_98])).

cnf(c_0_114,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_34]),c_0_30]),c_0_42])]),c_0_43]),c_0_84])).

cnf(c_0_115,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k9_tmap_1(esk1_0,esk2_0),X1) = k7_relat_1(k9_tmap_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])])).

cnf(c_0_116,negated_conjecture,
    ( r1_tmap_1(esk3_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk3_0),X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_53])).

cnf(c_0_117,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_105]),c_0_106]),c_0_30]),c_0_42])]),c_0_43]),c_0_107])])).

cnf(c_0_118,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk6_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk6_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_119,plain,
    ( esk6_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_120,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_funct_2(X4,X1,X6,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X6,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk1_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_29]),c_0_30]),c_0_42])]),c_0_43]),c_0_110])).

cnf(c_0_122,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk1_0,esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_29]),c_0_30]),c_0_42])]),c_0_43]),c_0_110])).

cnf(c_0_123,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_29]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_124,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_125,negated_conjecture,
    ( k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),X1) = k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_102]),c_0_101]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_126,negated_conjecture,
    ( r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_29]),c_0_81]),c_0_81]),c_0_45]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_127,negated_conjecture,
    ( k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),X1) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_105]),c_0_106]),c_0_30]),c_0_42])]),c_0_43]),c_0_107])])).

cnf(c_0_128,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_29])).

cnf(c_0_129,negated_conjecture,
    ( X1 = k9_tmap_1(esk1_0,esk2_0)
    | ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(k6_tmap_1(esk1_0,esk6_3(esk1_0,esk2_0,X1))),X1,k7_tmap_1(esk1_0,esk6_3(esk1_0,esk2_0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_84]),c_0_34]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_130,negated_conjecture,
    ( esk6_3(esk1_0,esk2_0,X1) = u1_struct_0(esk2_0)
    | X1 = k9_tmap_1(esk1_0,esk2_0)
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk1_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_84]),c_0_34]),c_0_30]),c_0_42])]),c_0_43])).

cnf(c_0_131,negated_conjecture,
    ( v1_xboole_0(X1)
    | r1_funct_2(X2,X1,u1_struct_0(esk1_0),u1_struct_0(esk1_0),X3,X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122]),c_0_123])]),c_0_124])).

cnf(c_0_132,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_133,negated_conjecture,
    ( k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k9_tmap_1(esk1_0,esk2_0),esk3_0) = k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_29])).

cnf(c_0_134,negated_conjecture,
    ( k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk1_0,k9_tmap_1(esk1_0,esk2_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_114]),c_0_102]),c_0_30]),c_0_42])]),c_0_43]),c_0_115]),c_0_101])])).

cnf(c_0_135,negated_conjecture,
    ( r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_38])).

cnf(c_0_136,negated_conjecture,
    ( k2_tmap_1(esk1_0,k8_tmap_1(esk1_0,esk2_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),esk3_0) = k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_29]),c_0_128])).

cnf(c_0_137,negated_conjecture,
    ( k7_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k9_tmap_1(esk1_0,esk2_0)
    | ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(k6_tmap_1(esk1_0,esk6_3(esk1_0,esk2_0,k7_tmap_1(esk1_0,u1_struct_0(esk2_0))))),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),k7_tmap_1(esk1_0,esk6_3(esk1_0,esk2_0,k7_tmap_1(esk1_0,u1_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_105]),c_0_106])]),c_0_107])])).

cnf(c_0_138,negated_conjecture,
    ( esk6_3(esk1_0,esk2_0,k7_tmap_1(esk1_0,u1_struct_0(esk2_0))) = u1_struct_0(esk2_0)
    | k7_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k9_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_105]),c_0_106])]),c_0_107])])).

cnf(c_0_139,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),k7_tmap_1(esk1_0,u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_107]),c_0_105]),c_0_106])]),c_0_124])).

cnf(c_0_140,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_141,negated_conjecture,
    ( k7_relat_1(k9_tmap_1(esk1_0,esk2_0),u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,esk1_0,k9_tmap_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_29])).

cnf(c_0_142,negated_conjecture,
    ( r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,esk1_0,k7_tmap_1(esk1_0,u1_struct_0(esk2_0)),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_143,negated_conjecture,
    ( k7_tmap_1(esk1_0,u1_struct_0(esk2_0)) = k9_tmap_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_81]),c_0_84]),c_0_139])])).

cnf(c_0_144,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,k8_tmap_1(esk1_0,esk2_0),k2_tmap_1(esk1_0,esk1_0,k9_tmap_1(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143]),c_0_144]),
    [proof]).
%------------------------------------------------------------------------------
