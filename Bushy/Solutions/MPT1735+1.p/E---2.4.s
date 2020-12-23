%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t44_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:15 EDT 2019

% Result     : Theorem 274.35s
% Output     : CNFRefutation 274.35s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 326 expanded)
%              Number of clauses        :   53 ( 117 expanded)
%              Number of leaves         :   17 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  401 (2268 expanded)
%              Number of equality atoms :   44 (  78 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_tsep_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X3,X2)
               => ( v1_tsep_1(k2_tsep_1(X1,X3,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X1,X3,X2),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',t44_tmap_1)).

fof(t30_tsep_1,axiom,(
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
             => ( ~ r1_tsep_1(X2,X3)
               => ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
                  & m1_pre_topc(k2_tsep_1(X1,X2,X3),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',t30_tsep_1)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',t16_tsep_1)).

fof(t32_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v3_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',t32_tops_2)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',dt_k9_subset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',t1_tsep_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',idempotence_k3_xboole_0)).

fof(d5_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_pre_topc(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( X4 = k2_tsep_1(X1,X2,X3)
                    <=> u1_struct_0(X4) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',d5_tsep_1)).

fof(dt_k2_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
        & v1_pre_topc(k2_tsep_1(X1,X2,X3))
        & m1_pre_topc(k2_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',dt_k2_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',cc1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',dt_l1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',t3_subset)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',commutativity_k3_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t44_tmap_1.p',redefinition_k9_subset_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v1_tsep_1(X3,X1)
                  & m1_pre_topc(X3,X1) )
               => ( ~ r1_tsep_1(X3,X2)
                 => ( v1_tsep_1(k2_tsep_1(X1,X3,X2),X2)
                    & m1_pre_topc(k2_tsep_1(X1,X3,X2),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tmap_1])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & v1_tsep_1(esk3_0,esk1_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ r1_tsep_1(esk3_0,esk2_0)
    & ( ~ v1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0)
      | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_19,plain,(
    ! [X65,X66,X67] :
      ( ( m1_pre_topc(k2_tsep_1(X65,X66,X67),X66)
        | r1_tsep_1(X66,X67)
        | v2_struct_0(X67)
        | ~ m1_pre_topc(X67,X65)
        | v2_struct_0(X66)
        | ~ m1_pre_topc(X66,X65)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( m1_pre_topc(k2_tsep_1(X65,X66,X67),X67)
        | r1_tsep_1(X66,X67)
        | v2_struct_0(X67)
        | ~ m1_pre_topc(X67,X65)
        | v2_struct_0(X66)
        | ~ m1_pre_topc(X66,X65)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

fof(c_0_20,plain,(
    ! [X53,X54,X55] :
      ( ( ~ v1_tsep_1(X54,X53)
        | ~ m1_pre_topc(X54,X53)
        | v3_pre_topc(X55,X53)
        | X55 != u1_struct_0(X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ m1_pre_topc(X54,X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) )
      & ( v1_tsep_1(X54,X53)
        | ~ v3_pre_topc(X55,X53)
        | X55 != u1_struct_0(X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ m1_pre_topc(X54,X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) )
      & ( m1_pre_topc(X54,X53)
        | ~ v3_pre_topc(X55,X53)
        | X55 != u1_struct_0(X54)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ m1_pre_topc(X54,X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X68,X69,X70,X72] :
      ( ( m1_subset_1(esk8_3(X68,X69,X70),k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v3_pre_topc(X70,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ m1_pre_topc(X69,X68)
        | ~ l1_pre_topc(X68) )
      & ( v3_pre_topc(esk8_3(X68,X69,X70),X68)
        | ~ v3_pre_topc(X70,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ m1_pre_topc(X69,X68)
        | ~ l1_pre_topc(X68) )
      & ( k9_subset_1(u1_struct_0(X69),esk8_3(X68,X69,X70),k2_struct_0(X69)) = X70
        | ~ v3_pre_topc(X70,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ m1_pre_topc(X69,X68)
        | ~ l1_pre_topc(X68) )
      & ( ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ v3_pre_topc(X72,X68)
        | k9_subset_1(u1_struct_0(X69),X72,k2_struct_0(X69)) != X70
        | v3_pre_topc(X70,X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X69)))
        | ~ m1_pre_topc(X69,X68)
        | ~ l1_pre_topc(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tops_2])])])])])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | m1_subset_1(k9_subset_1(X27,X28,X29),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_27,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X60,X61] :
      ( ~ l1_pre_topc(X60)
      | ~ m1_pre_topc(X61,X60)
      | m1_subset_1(u1_struct_0(X61),k1_zfmisc_1(u1_struct_0(X60))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_29,plain,(
    ! [X56,X57] : r1_tarski(k3_xboole_0(X56,X57),X56) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_30,plain,(
    ! [X44] : k3_xboole_0(X44,X44) = X44 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_31,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X20 != k2_tsep_1(X17,X18,X19)
        | u1_struct_0(X20) = k3_xboole_0(u1_struct_0(X18),u1_struct_0(X19))
        | v2_struct_0(X20)
        | ~ v1_pre_topc(X20)
        | ~ m1_pre_topc(X20,X17)
        | r1_tsep_1(X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) )
      & ( u1_struct_0(X20) != k3_xboole_0(u1_struct_0(X18),u1_struct_0(X19))
        | X20 = k2_tsep_1(X17,X18,X19)
        | v2_struct_0(X20)
        | ~ v1_pre_topc(X20)
        | ~ m1_pre_topc(X20,X17)
        | r1_tsep_1(X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

fof(c_0_32,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v2_struct_0(k2_tsep_1(X24,X25,X26))
        | v2_struct_0(X24)
        | ~ l1_pre_topc(X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X24) )
      & ( v1_pre_topc(k2_tsep_1(X24,X25,X26))
        | v2_struct_0(X24)
        | ~ l1_pre_topc(X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X24) )
      & ( m1_pre_topc(k2_tsep_1(X24,X25,X26),X24)
        | v2_struct_0(X24)
        | ~ l1_pre_topc(X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(X1,esk3_0,esk2_0),esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_39,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | l1_pre_topc(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_40,plain,(
    ! [X86,X87] :
      ( ~ v2_pre_topc(X86)
      | ~ l1_pre_topc(X86)
      | ~ m1_pre_topc(X87,X86)
      | v2_pre_topc(X87) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_41,plain,
    ( v3_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_45,plain,(
    ! [X16] :
      ( ~ l1_struct_0(X16)
      | k2_struct_0(X16) = u1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_46,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_47,plain,(
    ! [X73,X74] :
      ( ( ~ m1_subset_1(X73,k1_zfmisc_1(X74))
        | r1_tarski(X73,X74) )
      & ( ~ r1_tarski(X73,X74)
        | m1_subset_1(X73,k1_zfmisc_1(X74)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,plain,
    ( u1_struct_0(X1) = k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_52,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_54,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_57,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_59,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) != k9_subset_1(u1_struct_0(X1),X2,X3)
    | ~ v3_pre_topc(X4,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X5)
    | ~ l1_pre_topc(X5) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_60,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_44])).

cnf(c_0_61,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_64,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(X48))
      | k9_subset_1(X48,X49,X50) = k3_xboole_0(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_67,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_tsep_1(k2_tsep_1(esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_70,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_71,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_34]),c_0_36])])).

cnf(c_0_72,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_34]),c_0_36]),c_0_37])])).

cnf(c_0_73,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | k9_subset_1(u1_struct_0(X1),u1_struct_0(X4),k2_struct_0(X1)) != k9_subset_1(u1_struct_0(X1),X2,X3)
    | ~ v3_pre_topc(u1_struct_0(X4),X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ l1_pre_topc(X5) ),
    inference(spm,[status(thm)],[c_0_59,c_0_44])).

cnf(c_0_74,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_75,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_76,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(k2_tsep_1(X1,esk3_0,esk2_0)) = k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_67]),c_0_24]),c_0_23]),c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( X1 != u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_56]),c_0_71]),c_0_72])])).

cnf(c_0_80,negated_conjecture,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | k9_subset_1(u1_struct_0(X1),u1_struct_0(esk3_0),k2_struct_0(X1)) != k9_subset_1(u1_struct_0(X1),X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_35]),c_0_36])])).

cnf(c_0_81,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_71])).

cnf(c_0_82,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) = u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_34]),c_0_35]),c_0_36])]),c_0_38])).

cnf(c_0_84,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),X1,X2) != u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_68]),c_0_83]),c_0_34])]),c_0_42])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(X1,u1_struct_0(esk2_0)) != u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_82]),c_0_77])])).

cnf(c_0_86,negated_conjecture,
    ( k3_xboole_0(u1_struct_0(esk2_0),X1) != u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_68])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_83,c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
