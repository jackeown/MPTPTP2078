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
% DateTime   : Thu Dec  3 11:18:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 589 expanded)
%              Number of clauses        :   53 ( 214 expanded)
%              Number of leaves         :   14 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  496 (5861 expanded)
%              Number of equality atoms :   26 ( 534 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   90 (   3 average)
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

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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

fof(t86_tmap_1,axiom,(
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
                     => ( ( v1_tsep_1(X3,X4)
                          & m1_pre_topc(X3,X4) )
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( X6 = X7
                                 => ( r1_tmap_1(X4,X2,X5,X6)
                                  <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X25,X26] :
      ( ( ~ m1_pre_topc(X25,X26)
        | m1_pre_topc(X25,g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(X25) )
      & ( ~ m1_pre_topc(X25,g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))
        | m1_pre_topc(X25,X26)
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk4_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))
    & g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0
    & m1_subset_1(esk9_0,u1_struct_0(esk7_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk6_0))
    & esk9_0 = esk10_0
    & r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)
    & ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_18,plain,(
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

fof(c_0_19,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | m1_pre_topc(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_20,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

fof(c_0_29,plain,(
    ! [X32] :
      ( ~ l1_pre_topc(X32)
      | m1_pre_topc(X32,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_30,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(X1,esk7_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_36,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk7_0))
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28])])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_33]),c_0_23])])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_23]),c_0_34])])).

fof(c_0_43,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))
      | m1_pre_topc(X24,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_44,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] :
      ( ( ~ r1_tmap_1(X42,X40,X43,X44)
        | r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)
        | X44 != X45
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ v1_tsep_1(X41,X42)
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
      & ( ~ r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)
        | r1_tmap_1(X42,X40,X43,X44)
        | X44 != X45
        | ~ m1_subset_1(X45,u1_struct_0(X41))
        | ~ m1_subset_1(X44,u1_struct_0(X42))
        | ~ v1_tsep_1(X41,X42)
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
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk7_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ r1_tarski(u1_struct_0(esk7_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk6_0))
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ v1_tsep_1(X1,X4)
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

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk7_0)
    | ~ m1_pre_topc(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_40])])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_28])])).

fof(c_0_51,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_tsep_1(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | v3_pre_topc(X29,X27)
        | X29 != u1_struct_0(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_pre_topc(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( v1_tsep_1(X28,X27)
        | ~ v3_pre_topc(X29,X27)
        | X29 != u1_struct_0(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_pre_topc(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_pre_topc(X28,X27)
        | ~ v3_pre_topc(X29,X27)
        | X29 != u1_struct_0(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_pre_topc(X28,X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_52,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | m1_subset_1(u1_struct_0(X31),k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_53,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_tsep_1(X6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_48,c_0_25])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk7_0)
    | ~ m1_pre_topc(esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_64,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_66,plain,(
    ! [X19,X20] :
      ( ( ~ v3_pre_topc(X20,X19)
        | r2_hidden(X20,u1_pre_topc(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(X20,u1_pre_topc(X19))
        | v3_pre_topc(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,esk5_0,k3_tmap_1(X2,esk5_0,esk7_0,X3,esk8_0),X1)
    | ~ v1_tsep_1(X3,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_pre_topc(esk7_0,X2)
    | ~ m1_pre_topc(X3,esk7_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])]),c_0_59]),c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_36]),c_0_41])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]),c_0_65])).

cnf(c_0_75,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70]),c_0_69]),c_0_33]),c_0_40]),c_0_23]),c_0_34])]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_77,plain,
    ( v1_tsep_1(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_65])).

fof(c_0_78,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r1_tarski(X13,u1_pre_topc(X12))
        | r2_hidden(k5_setfam_1(u1_struct_0(X12),X13),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X14,u1_pre_topc(X12))
        | ~ r2_hidden(X15,u1_pre_topc(X12))
        | r2_hidden(k9_subset_1(u1_struct_0(X12),X14,X15),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_70]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_80,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.030 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.19/0.40  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.40  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.19/0.40  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.40  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.40  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.19/0.40  fof(t86_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_tsep_1(X3,X4)&m1_pre_topc(X3,X4))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(X6=X7=>(r1_tmap_1(X4,X2,X5,X6)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 0.19/0.40  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.19/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.40  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.19/0.40  fof(c_0_15, plain, ![X25, X26]:((~m1_pre_topc(X25,X26)|m1_pre_topc(X25,g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))|~l1_pre_topc(X26)|~l1_pre_topc(X25))&(~m1_pre_topc(X25,g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))|m1_pre_topc(X25,X26)|~l1_pre_topc(X26)|~l1_pre_topc(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.40  fof(c_0_16, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.40  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))))&(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0&(m1_subset_1(esk9_0,u1_struct_0(esk7_0))&(m1_subset_1(esk10_0,u1_struct_0(esk6_0))&((esk9_0=esk10_0&r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0))&~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.40  fof(c_0_18, plain, ![X33, X34, X35]:((~r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|m1_pre_topc(X34,X35)|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~m1_pre_topc(X34,X35)|r1_tarski(u1_struct_0(X34),u1_struct_0(X35))|~m1_pre_topc(X35,X33)|~m1_pre_topc(X34,X33)|(~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.19/0.40  fof(c_0_19, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_pre_topc(X38,X37)|m1_pre_topc(X38,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.40  cnf(c_0_20, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_21, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_24, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_25, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_26, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.19/0.40  fof(c_0_29, plain, ![X32]:(~l1_pre_topc(X32)|m1_pre_topc(X32,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.40  fof(c_0_30, plain, ![X10, X11]:(~v2_pre_topc(X10)|~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|v2_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.40  fof(c_0_31, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_32, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (m1_pre_topc(X1,esk7_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.19/0.40  cnf(c_0_36, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_37, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk7_0))|~m1_pre_topc(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_23]), c_0_34])])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28])])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_33]), c_0_23])])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_23]), c_0_34])])).
% 0.19/0.40  fof(c_0_43, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))|m1_pre_topc(X24,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.19/0.40  fof(c_0_44, plain, ![X39, X40, X41, X42, X43, X44, X45]:((~r1_tmap_1(X42,X40,X43,X44)|r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)|X44!=X45|~m1_subset_1(X45,u1_struct_0(X41))|~m1_subset_1(X44,u1_struct_0(X42))|(~v1_tsep_1(X41,X42)|~m1_pre_topc(X41,X42))|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40)))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X39))|(v2_struct_0(X41)|~m1_pre_topc(X41,X39))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(~r1_tmap_1(X41,X40,k3_tmap_1(X39,X40,X42,X41,X43),X45)|r1_tmap_1(X42,X40,X43,X44)|X44!=X45|~m1_subset_1(X45,u1_struct_0(X41))|~m1_subset_1(X44,u1_struct_0(X42))|(~v1_tsep_1(X41,X42)|~m1_pre_topc(X41,X42))|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X40)))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X39))|(v2_struct_0(X41)|~m1_pre_topc(X41,X39))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t86_tmap_1])])])])])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk7_0)=u1_struct_0(X1)|~m1_pre_topc(X1,esk7_0)|~r1_tarski(u1_struct_0(esk7_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk6_0))|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_40]), c_0_41]), c_0_42])])).
% 0.19/0.40  cnf(c_0_47, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_48, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~v1_tsep_1(X1,X4)|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk7_0)|~m1_pre_topc(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_40])])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (m1_pre_topc(X1,esk6_0)|~m1_pre_topc(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_28])])).
% 0.19/0.40  fof(c_0_51, plain, ![X27, X28, X29]:((~v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|v3_pre_topc(X29,X27)|X29!=u1_struct_0(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_pre_topc(X28,X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&((v1_tsep_1(X28,X27)|~v3_pre_topc(X29,X27)|X29!=u1_struct_0(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_pre_topc(X28,X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(m1_pre_topc(X28,X27)|~v3_pre_topc(X29,X27)|X29!=u1_struct_0(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_pre_topc(X28,X27)|(~v2_pre_topc(X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.19/0.40  fof(c_0_52, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|m1_subset_1(u1_struct_0(X31),k1_zfmisc_1(u1_struct_0(X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.40  cnf(c_0_53, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v1_tsep_1(X6,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_48, c_0_25])])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk7_0)|~m1_pre_topc(esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.40  cnf(c_0_64, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.40  cnf(c_0_65, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.40  fof(c_0_66, plain, ![X19, X20]:((~v3_pre_topc(X20,X19)|r2_hidden(X20,u1_pre_topc(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~r2_hidden(X20,u1_pre_topc(X19))|v3_pre_topc(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,esk5_0,k3_tmap_1(X2,esk5_0,esk7_0,X3,esk8_0),X1)|~v1_tsep_1(X3,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))|~m1_subset_1(X1,u1_struct_0(X3))|~m1_pre_topc(esk7_0,X2)|~m1_pre_topc(X3,esk7_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])]), c_0_59]), c_0_60])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_36]), c_0_41])])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_74, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_64]), c_0_65])).
% 0.19/0.40  cnf(c_0_75, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (~v1_tsep_1(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70]), c_0_69]), c_0_33]), c_0_40]), c_0_23]), c_0_34])]), c_0_71]), c_0_72]), c_0_73])).
% 0.19/0.40  cnf(c_0_77, plain, (v1_tsep_1(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_65])).
% 0.19/0.40  fof(c_0_78, plain, ![X12, X13, X14, X15]:((((r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))|~v2_pre_topc(X12)|~l1_pre_topc(X12))&(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|(~r1_tarski(X13,u1_pre_topc(X12))|r2_hidden(k5_setfam_1(u1_struct_0(X12),X13),u1_pre_topc(X12)))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(X14,u1_pre_topc(X12))|~r2_hidden(X15,u1_pre_topc(X12))|r2_hidden(k9_subset_1(u1_struct_0(X12),X14,X15),u1_pre_topc(X12))))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&(((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_70]), c_0_40]), c_0_41]), c_0_42])])).
% 0.19/0.40  cnf(c_0_80, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_41]), c_0_42])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 82
% 0.19/0.40  # Proof object clause steps            : 53
% 0.19/0.40  # Proof object formula steps           : 29
% 0.19/0.40  # Proof object conjectures             : 38
% 0.19/0.40  # Proof object clause conjectures      : 35
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 31
% 0.19/0.40  # Proof object initial formulas used   : 14
% 0.19/0.40  # Proof object generating inferences   : 17
% 0.19/0.40  # Proof object simplifying inferences  : 57
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 14
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 57
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 56
% 0.19/0.40  # Processed clauses                    : 327
% 0.19/0.40  # ...of these trivial                  : 5
% 0.19/0.40  # ...subsumed                          : 107
% 0.19/0.40  # ...remaining for further processing  : 215
% 0.19/0.40  # Other redundant clauses eliminated   : 6
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 3
% 0.19/0.40  # Backward-rewritten                   : 7
% 0.19/0.40  # Generated clauses                    : 433
% 0.19/0.40  # ...of the previous two non-trivial   : 269
% 0.19/0.40  # Contextual simplify-reflections      : 13
% 0.19/0.40  # Paramodulations                      : 427
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 6
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 145
% 0.19/0.40  #    Positive orientable unit clauses  : 25
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 7
% 0.19/0.40  #    Non-unit-clauses                  : 113
% 0.19/0.40  # Current number of unprocessed clauses: 51
% 0.19/0.40  # ...number of literals in the above   : 317
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 64
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 7055
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1053
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 123
% 0.19/0.40  # Unit Clause-clause subsumption calls : 143
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 3
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 15641
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.052 s
% 0.19/0.40  # System time              : 0.007 s
% 0.19/0.40  # Total time               : 0.059 s
% 0.19/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
