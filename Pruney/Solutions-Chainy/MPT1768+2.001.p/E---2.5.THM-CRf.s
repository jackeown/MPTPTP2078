%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 688 expanded)
%              Number of clauses        :   60 ( 228 expanded)
%              Number of leaves         :   13 ( 168 expanded)
%              Depth                    :   14
%              Number of atoms          :  432 (7904 expanded)
%              Number of equality atoms :   41 (  96 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X5,X4) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

fof(t38_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(t78_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X5,X4) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t79_tmap_1])).

fof(c_0_14,plain,(
    ! [X11,X12,X13,X14] :
      ( ( v1_funct_1(k2_partfun1(X11,X12,X14,X13))
        | X12 = k1_xboole_0
        | ~ r1_tarski(X13,X11)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v1_funct_2(k2_partfun1(X11,X12,X14,X13),X13,X12)
        | X12 = k1_xboole_0
        | ~ r1_tarski(X13,X11)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( m1_subset_1(k2_partfun1(X11,X12,X14,X13),k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
        | X12 = k1_xboole_0
        | ~ r1_tarski(X13,X11)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v1_funct_1(k2_partfun1(X11,X12,X14,X13))
        | X11 != k1_xboole_0
        | ~ r1_tarski(X13,X11)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v1_funct_2(k2_partfun1(X11,X12,X14,X13),X13,X12)
        | X11 != k1_xboole_0
        | ~ r1_tarski(X13,X11)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( m1_subset_1(k2_partfun1(X11,X12,X14,X13),k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
        | X11 != k1_xboole_0
        | ~ r1_tarski(X13,X11)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | r1_tarski(u1_struct_0(X31),u1_struct_0(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_funct_2(k2_partfun1(X1,X2,X3,X4),X4,X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_26,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X25)
      | ~ m1_pre_topc(X28,X25)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
      | ~ m1_pre_topc(X28,X27)
      | k3_tmap_1(X25,X26,X27,X28,X29) = k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),X29,u1_struct_0(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_27,plain,(
    ! [X37,X38,X39] :
      ( ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | ~ m1_pre_topc(X39,X38)
      | m1_pre_topc(X39,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | v2_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_30,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,X1),X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_31])])).

cnf(c_0_41,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_24]),c_0_37])])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

fof(c_0_49,plain,(
    ! [X7,X8,X9,X10] :
      ( ( v1_funct_1(k2_partfun1(X7,X8,X9,X10))
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( m1_subset_1(k2_partfun1(X7,X8,X9,X10),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_50,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ m1_pre_topc(X34,X32)
      | v2_struct_0(X35)
      | ~ m1_pre_topc(X35,X32)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X32),u1_struct_0(X33))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
      | ~ m1_pre_topc(X34,X35)
      | r2_funct_2(u1_struct_0(X34),u1_struct_0(X33),k3_tmap_1(X32,X33,X35,X34,k2_tmap_1(X32,X33,X36,X35)),k2_tmap_1(X32,X33,X36,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).

fof(c_0_51,plain,(
    ! [X21,X22,X23,X24] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
      | ~ m1_pre_topc(X24,X21)
      | k2_tmap_1(X21,X22,X23,X24) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_52,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_18]),c_0_42]),c_0_43]),c_0_19]),c_0_20])]),c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_39]),c_0_31])])).

cnf(c_0_54,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(X2))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_42]),c_0_43])]),c_0_44]),c_0_48])).

cnf(c_0_55,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_62,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(X2))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_18]),c_0_20])])).

cnf(c_0_63,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,X1,k2_tmap_1(X3,X2,X5,X4)),k2_tmap_1(X3,X2,X5,X1))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_56,c_0_34])).

cnf(c_0_64,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk6_0,X1) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_18]),c_0_42]),c_0_31]),c_0_43]),c_0_46]),c_0_19]),c_0_20])]),c_0_44]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_23]),c_0_24]),c_0_37])]),c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_23]),c_0_24]),c_0_37])]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_35])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,X2,X1,k2_tmap_1(esk3_0,esk2_0,esk6_0,X2)),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_42]),c_0_31]),c_0_43]),c_0_46]),c_0_19]),c_0_18]),c_0_20])]),c_0_44]),c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0))
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_24]),c_0_37])]),c_0_60])).

fof(c_0_73,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,X2,X1,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0))
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_39]),c_0_31]),c_0_46])]),c_0_58])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_77,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0)),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_39]),c_0_53]),c_0_35])]),c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_81,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_82,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_83,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])]),c_0_44])).

cnf(c_0_84,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.46  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.028 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t79_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 0.20/0.46  fof(t38_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 0.20/0.46  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.46  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.20/0.46  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.46  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.46  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.46  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.20/0.46  fof(t78_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 0.20/0.46  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.46  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.46  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.46  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.46  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)))))))))), inference(assume_negation,[status(cth)],[t79_tmap_1])).
% 0.20/0.46  fof(c_0_14, plain, ![X11, X12, X13, X14]:((((v1_funct_1(k2_partfun1(X11,X12,X14,X13))|X12=k1_xboole_0|~r1_tarski(X13,X11)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(v1_funct_2(k2_partfun1(X11,X12,X14,X13),X13,X12)|X12=k1_xboole_0|~r1_tarski(X13,X11)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))&(m1_subset_1(k2_partfun1(X11,X12,X14,X13),k1_zfmisc_1(k2_zfmisc_1(X13,X12)))|X12=k1_xboole_0|~r1_tarski(X13,X11)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))&(((v1_funct_1(k2_partfun1(X11,X12,X14,X13))|X11!=k1_xboole_0|~r1_tarski(X13,X11)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(v1_funct_2(k2_partfun1(X11,X12,X14,X13),X13,X12)|X11!=k1_xboole_0|~r1_tarski(X13,X11)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))&(m1_subset_1(k2_partfun1(X11,X12,X14,X13),k1_zfmisc_1(k2_zfmisc_1(X13,X12)))|X11!=k1_xboole_0|~r1_tarski(X13,X11)|(~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).
% 0.20/0.46  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((m1_pre_topc(esk4_0,esk3_0)&m1_pre_topc(esk5_0,esk4_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.20/0.46  fof(c_0_16, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|l1_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.46  cnf(c_0_17, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|X2=k1_xboole_0|~r1_tarski(X4,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.46  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  fof(c_0_21, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|r1_tarski(u1_struct_0(X31),u1_struct_0(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.20/0.46  cnf(c_0_22, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.46  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_25, plain, (v1_funct_2(k2_partfun1(X1,X2,X3,X4),X4,X2)|X2=k1_xboole_0|~r1_tarski(X4,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.46  fof(c_0_26, plain, ![X25, X26, X27, X28, X29]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(~m1_pre_topc(X27,X25)|(~m1_pre_topc(X28,X25)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))|(~m1_pre_topc(X28,X27)|k3_tmap_1(X25,X26,X27,X28,X29)=k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),X29,u1_struct_0(X28)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.46  fof(c_0_27, plain, ![X37, X38, X39]:(~v2_pre_topc(X37)|~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|(~m1_pre_topc(X39,X38)|m1_pre_topc(X39,X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.46  fof(c_0_28, plain, ![X15, X16]:(~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|v2_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.46  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))|~r1_tarski(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.46  cnf(c_0_30, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.46  cnf(c_0_32, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,X1),X1,u1_struct_0(esk2_0))|~r1_tarski(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.46  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_34, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.46  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_36, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.46  cnf(c_0_37, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.20/0.46  cnf(c_0_39, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_31])])).
% 0.20/0.46  cnf(c_0_41, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.46  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, (m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.46  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_24]), c_0_37])])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.46  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.20/0.46  fof(c_0_49, plain, ![X7, X8, X9, X10]:((v1_funct_1(k2_partfun1(X7,X8,X9,X10))|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(m1_subset_1(k2_partfun1(X7,X8,X9,X10),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.20/0.46  fof(c_0_50, plain, ![X32, X33, X34, X35, X36]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(v2_struct_0(X34)|~m1_pre_topc(X34,X32)|(v2_struct_0(X35)|~m1_pre_topc(X35,X32)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|(~m1_pre_topc(X34,X35)|r2_funct_2(u1_struct_0(X34),u1_struct_0(X33),k3_tmap_1(X32,X33,X35,X34,k2_tmap_1(X32,X33,X36,X35)),k2_tmap_1(X32,X33,X36,X34)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).
% 0.20/0.46  fof(c_0_51, plain, ![X21, X22, X23, X24]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|(~m1_pre_topc(X24,X21)|k2_tmap_1(X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.46  cnf(c_0_52, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_18]), c_0_42]), c_0_43]), c_0_19]), c_0_20])]), c_0_44])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_39]), c_0_31])])).
% 0.20/0.46  cnf(c_0_54, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(X2))|u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_1(k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_42]), c_0_43])]), c_0_44]), c_0_48])).
% 0.20/0.46  cnf(c_0_55, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.46  cnf(c_0_56, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.46  cnf(c_0_57, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.46  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.46  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_39])).
% 0.20/0.46  cnf(c_0_62, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(X2))|u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_18]), c_0_20])])).
% 0.20/0.46  cnf(c_0_63, plain, (r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,X1,k2_tmap_1(X3,X2,X5,X4)),k2_tmap_1(X3,X2,X5,X1))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X4)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_56, c_0_34])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,esk6_0,X1)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_18]), c_0_42]), c_0_31]), c_0_43]), c_0_46]), c_0_19]), c_0_20])]), c_0_44]), c_0_58])).
% 0.20/0.46  cnf(c_0_65, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_66, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_23]), c_0_24]), c_0_37])]), c_0_60])).
% 0.20/0.46  cnf(c_0_67, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_23]), c_0_24]), c_0_37])]), c_0_60])).
% 0.20/0.46  cnf(c_0_68, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0))|u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_35])).
% 0.20/0.46  cnf(c_0_69, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,X2,X1,k2_tmap_1(esk3_0,esk2_0,esk6_0,X2)),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_42]), c_0_31]), c_0_43]), c_0_46]), c_0_19]), c_0_18]), c_0_20])]), c_0_44]), c_0_58])).
% 0.20/0.46  cnf(c_0_71, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.20/0.46  cnf(c_0_72, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0))|u1_struct_0(esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_24]), c_0_37])]), c_0_60])).
% 0.20/0.46  fof(c_0_73, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,X2,X1,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_64])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0))|u1_struct_0(esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_39]), c_0_31]), c_0_46])]), c_0_58])).
% 0.20/0.46  cnf(c_0_76, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_77, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)),u1_struct_0(esk5_0)),k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.46  cnf(c_0_79, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_39]), c_0_53]), c_0_35])]), c_0_76]), c_0_77]), c_0_78])).
% 0.20/0.46  cnf(c_0_81, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.46  fof(c_0_82, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.46  cnf(c_0_83, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])]), c_0_44])).
% 0.20/0.46  cnf(c_0_84, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.46  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_42])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 86
% 0.20/0.46  # Proof object clause steps            : 60
% 0.20/0.46  # Proof object formula steps           : 26
% 0.20/0.46  # Proof object conjectures             : 48
% 0.20/0.46  # Proof object clause conjectures      : 45
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 30
% 0.20/0.46  # Proof object initial formulas used   : 13
% 0.20/0.46  # Proof object generating inferences   : 27
% 0.20/0.46  # Proof object simplifying inferences  : 83
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 13
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 36
% 0.20/0.46  # Removed in clause preprocessing      : 0
% 0.20/0.46  # Initial clauses in saturation        : 36
% 0.20/0.46  # Processed clauses                    : 706
% 0.20/0.46  # ...of these trivial                  : 5
% 0.20/0.46  # ...subsumed                          : 232
% 0.20/0.46  # ...remaining for further processing  : 469
% 0.20/0.46  # Other redundant clauses eliminated   : 0
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 8
% 0.20/0.46  # Backward-rewritten                   : 300
% 0.20/0.46  # Generated clauses                    : 879
% 0.20/0.46  # ...of the previous two non-trivial   : 916
% 0.20/0.46  # Contextual simplify-reflections      : 45
% 0.20/0.46  # Paramodulations                      : 879
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 0
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 127
% 0.20/0.46  #    Positive orientable unit clauses  : 19
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 6
% 0.20/0.46  #    Non-unit-clauses                  : 102
% 0.20/0.46  # Current number of unprocessed clauses: 277
% 0.20/0.46  # ...number of literals in the above   : 1555
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 342
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 35028
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 8134
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 285
% 0.20/0.46  # Unit Clause-clause subsumption calls : 124
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 25
% 0.20/0.46  # BW rewrite match successes           : 2
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 42674
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.114 s
% 0.20/0.47  # System time              : 0.007 s
% 0.20/0.47  # Total time               : 0.120 s
% 0.20/0.47  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
