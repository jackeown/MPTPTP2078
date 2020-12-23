%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 630 expanded)
%              Number of clauses        :   55 ( 206 expanded)
%              Number of leaves         :   13 ( 155 expanded)
%              Depth                    :   12
%              Number of atoms          :  405 (7459 expanded)
%              Number of equality atoms :   26 ( 744 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                 => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

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

fof(t22_tsep_1,axiom,(
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
             => m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t83_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( r1_tarski(X6,u1_struct_0(X3))
                                        & m1_connsp_2(X6,X4,X7)
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X2,X5,X7)
                                      <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(existence_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ? [X3] : m1_connsp_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                   => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tmap_1])).

fof(c_0_14,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ m1_pre_topc(X32,X31)
      | k1_tsep_1(X31,X32,X32) = g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk2_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
    & g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = esk5_0
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk4_0))
    & esk7_0 = esk8_0
    & r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)
    & ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

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

fof(c_0_17,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | m1_pre_topc(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_18,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X25)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X25)
      | m1_pre_topc(X26,k1_tsep_1(X25,X26,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | v2_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_28,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( k1_tsep_1(esk2_0,esk4_0,esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_32,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_36,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_20]),c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_22])])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_22]),c_0_23])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

fof(c_0_42,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | m1_pre_topc(X18,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( ~ r1_tmap_1(X42,X40,X43,X45)
        | r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X46)
        | ~ r1_tarski(X44,u1_struct_0(X41))
        | ~ m1_connsp_2(X44,X42,X45)
        | X45 != X46
        | ~ m1_subset_1(X46,u1_struct_0(X41))
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_pre_topc(X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40))))
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X39)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X39)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X46)
        | r1_tmap_1(X42,X40,X43,X45)
        | ~ r1_tarski(X44,u1_struct_0(X41))
        | ~ m1_connsp_2(X44,X42,X45)
        | X45 != X46
        | ~ m1_subset_1(X46,u1_struct_0(X41))
        | ~ m1_subset_1(X45,u1_struct_0(X42))
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_pre_topc(X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40))))
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X39)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X39)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_tmap_1])])])])])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk4_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ r1_tarski(u1_struct_0(esk4_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_22]),c_0_23])])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_22])])).

cnf(c_0_49,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | ~ r1_tarski(X8,u1_struct_0(X1))
    | ~ m1_connsp_2(X8,X4,X7)
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0)
    | ~ m1_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_37])])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_21]),c_0_48])])).

cnf(c_0_54,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_55,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_connsp_2(X21,X19,X20)
      | m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_56,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | m1_connsp_2(esk1_2(X22,X23),X22,X23) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

cnf(c_0_57,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X7,X1,X4)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ r1_tarski(X7,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_51,c_0_29])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0)
    | ~ m1_pre_topc(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_33]),c_0_22]),c_0_23])])).

fof(c_0_69,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(esk1_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_73,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,esk3_0,k3_tmap_1(X2,esk3_0,esk5_0,X3,esk6_0),X1)
    | ~ m1_connsp_2(X4,esk5_0,X1)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X3,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r1_tarski(X4,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62])]),c_0_63]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_38]),c_0_39])]),c_0_64])).

cnf(c_0_79,negated_conjecture,
    ( m1_connsp_2(esk1_2(esk5_0,esk7_0),esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_71]),c_0_38]),c_0_39])]),c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_33]),c_0_37]),c_0_22]),c_0_23]),c_0_71]),c_0_75]),c_0_71]),c_0_75])]),c_0_76]),c_0_25]),c_0_24]),c_0_77]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_79,c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.41  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.20/0.41  fof(t25_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 0.20/0.41  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.41  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.41  fof(t22_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 0.20/0.41  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.41  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.20/0.41  fof(t83_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>(((r1_tarski(X6,u1_struct_0(X3))&m1_connsp_2(X6,X4,X7))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 0.20/0.41  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.20/0.41  fof(existence_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>?[X3]:m1_connsp_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.20/0.41  fof(c_0_14, plain, ![X31, X32]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~m1_pre_topc(X32,X31)|k1_tsep_1(X31,X32,X32)=g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_tmap_1])])])])).
% 0.20/0.41  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=esk5_0&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk4_0))&((esk7_0=esk8_0&r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0))&~r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.20/0.41  fof(c_0_16, plain, ![X33, X34, X35]:((~r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|m1_pre_topc(X34,X35)|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~m1_pre_topc(X34,X35)|r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.41  fof(c_0_17, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_pre_topc(X38,X37)|m1_pre_topc(X38,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.41  fof(c_0_18, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X25)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25)|m1_pre_topc(X26,k1_tsep_1(X25,X26,X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).
% 0.20/0.41  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_tsep_1(X1,X2,X2)=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=esk5_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  fof(c_0_26, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.41  fof(c_0_27, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|v2_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.41  cnf(c_0_28, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_29, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_30, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (k1_tsep_1(esk2_0,esk4_0,esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_25])).
% 0.20/0.41  cnf(c_0_32, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_34, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  fof(c_0_35, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_20]), c_0_22]), c_0_23])]), c_0_24]), c_0_25])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_22])])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_22]), c_0_23])])).
% 0.20/0.41  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.20/0.41  fof(c_0_42, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|m1_pre_topc(X18,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.20/0.41  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  fof(c_0_44, plain, ![X39, X40, X41, X42, X43, X44, X45, X46]:((~r1_tmap_1(X42,X40,X43,X45)|r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X46)|(~r1_tarski(X44,u1_struct_0(X41))|~m1_connsp_2(X44,X42,X45)|X45!=X46)|~m1_subset_1(X46,u1_struct_0(X41))|~m1_subset_1(X45,u1_struct_0(X42))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_pre_topc(X41,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40)))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X39))|(v2_struct_0(X41)|~m1_pre_topc(X41,X39))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(~r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X46)|r1_tmap_1(X42,X40,X43,X45)|(~r1_tarski(X44,u1_struct_0(X41))|~m1_connsp_2(X44,X42,X45)|X45!=X46)|~m1_subset_1(X46,u1_struct_0(X41))|~m1_subset_1(X45,u1_struct_0(X42))|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_pre_topc(X41,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40)))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X39))|(v2_struct_0(X41)|~m1_pre_topc(X41,X39))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_tmap_1])])])])])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk4_0)|~m1_pre_topc(X1,esk4_0)|~r1_tarski(u1_struct_0(esk4_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk5_0))|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_22]), c_0_23])])).
% 0.20/0.41  cnf(c_0_47, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_22])])).
% 0.20/0.41  cnf(c_0_49, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.20/0.41  cnf(c_0_51, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~r1_tarski(X8,u1_struct_0(X1))|~m1_connsp_2(X8,X4,X7)|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk5_0)|~m1_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_37])])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_21]), c_0_48])])).
% 0.20/0.41  cnf(c_0_54, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.41  fof(c_0_55, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))|(~m1_connsp_2(X21,X19,X20)|m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.20/0.41  fof(c_0_56, plain, ![X22, X23]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,u1_struct_0(X22))|m1_connsp_2(esk1_2(X22,X23),X22,X23)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).
% 0.20/0.41  cnf(c_0_57, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X7,X1,X4)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~r1_tarski(X7,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_51, c_0_29])])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk5_0)|~m1_pre_topc(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_33]), c_0_22]), c_0_23])])).
% 0.20/0.41  fof(c_0_69, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_70, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_72, plain, (v2_struct_0(X1)|m1_connsp_2(esk1_2(X1,X2),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,esk3_0,k3_tmap_1(X2,esk3_0,esk5_0,X3,esk6_0),X1)|~m1_connsp_2(X4,esk5_0,X1)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X3,esk5_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(X3))|~r1_tarski(X4,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_62])]), c_0_63]), c_0_64])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (~r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_connsp_2(X1,esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_38]), c_0_39])]), c_0_64])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (m1_connsp_2(esk1_2(esk5_0,esk7_0),esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_71]), c_0_38]), c_0_39])]), c_0_64])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (~m1_connsp_2(X1,esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_33]), c_0_37]), c_0_22]), c_0_23]), c_0_71]), c_0_75]), c_0_71]), c_0_75])]), c_0_76]), c_0_25]), c_0_24]), c_0_77]), c_0_78])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_79, c_0_80]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 82
% 0.20/0.41  # Proof object clause steps            : 55
% 0.20/0.41  # Proof object formula steps           : 27
% 0.20/0.41  # Proof object conjectures             : 40
% 0.20/0.41  # Proof object clause conjectures      : 37
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 32
% 0.20/0.41  # Proof object initial formulas used   : 13
% 0.20/0.41  # Proof object generating inferences   : 17
% 0.20/0.41  # Proof object simplifying inferences  : 69
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 14
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 38
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 38
% 0.20/0.41  # Processed clauses                    : 437
% 0.20/0.41  # ...of these trivial                  : 18
% 0.20/0.41  # ...subsumed                          : 159
% 0.20/0.41  # ...remaining for further processing  : 260
% 0.20/0.41  # Other redundant clauses eliminated   : 4
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 8
% 0.20/0.41  # Backward-rewritten                   : 35
% 0.20/0.41  # Generated clauses                    : 786
% 0.20/0.41  # ...of the previous two non-trivial   : 491
% 0.20/0.41  # Contextual simplify-reflections      : 25
% 0.20/0.41  # Paramodulations                      : 769
% 0.20/0.41  # Factorizations                       : 12
% 0.20/0.41  # Equation resolutions                 : 4
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 175
% 0.20/0.41  #    Positive orientable unit clauses  : 41
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 6
% 0.20/0.41  #    Non-unit-clauses                  : 128
% 0.20/0.41  # Current number of unprocessed clauses: 111
% 0.20/0.41  # ...number of literals in the above   : 814
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 81
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4234
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1195
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 190
% 0.20/0.41  # Unit Clause-clause subsumption calls : 34
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 17
% 0.20/0.41  # BW rewrite match successes           : 9
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 19467
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.059 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.066 s
% 0.20/0.41  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
