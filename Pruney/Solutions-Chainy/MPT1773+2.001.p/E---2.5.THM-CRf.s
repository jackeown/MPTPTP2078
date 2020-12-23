%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 568 expanded)
%              Number of clauses        :   60 ( 184 expanded)
%              Number of leaves         :   13 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  543 (8709 expanded)
%              Number of equality atoms :   28 ( 369 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal clause size      :   44 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_tmap_1,conjecture,(
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
                                   => ( ( v3_pre_topc(X6,X4)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X2,X5,X7)
                                      <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

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

fof(t64_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

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
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X3))
                                     => ( ( v3_pre_topc(X6,X4)
                                          & r2_hidden(X7,X6)
                                          & r1_tarski(X6,u1_struct_0(X3))
                                          & X7 = X8 )
                                       => ( r1_tmap_1(X4,X2,X5,X7)
                                        <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t84_tmap_1])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

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
    & m1_pre_topc(esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk4_0))
    & v3_pre_topc(esk7_0,esk5_0)
    & r2_hidden(esk8_0,esk7_0)
    & r1_tarski(esk7_0,u1_struct_0(esk4_0))
    & esk8_0 = esk9_0
    & ( ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)
      | ~ r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0) )
    & ( r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)
      | r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v3_pre_topc(X25,X24)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(X25,k1_tops_1(X24,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_17,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk7_0,k1_tops_1(esk5_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X17,X18] :
      ( ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | v2_pre_topc(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_32,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54,X55] :
      ( ( ~ r1_tmap_1(X51,X49,X52,X54)
        | r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)
        | ~ r1_tarski(X53,u1_struct_0(X50))
        | ~ m1_connsp_2(X53,X51,X54)
        | X54 != X55
        | ~ m1_subset_1(X55,u1_struct_0(X50))
        | ~ m1_subset_1(X54,u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ m1_pre_topc(X50,X51)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49))))
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X48)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( ~ r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)
        | r1_tmap_1(X51,X49,X52,X54)
        | ~ r1_tarski(X53,u1_struct_0(X50))
        | ~ m1_connsp_2(X53,X51,X54)
        | X54 != X55
        | ~ m1_subset_1(X55,u1_struct_0(X50))
        | ~ m1_subset_1(X54,u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ m1_pre_topc(X50,X51)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49))))
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X48)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_tmap_1])])])])])).

fof(c_0_33,plain,(
    ! [X45,X46,X47] :
      ( ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | ~ m1_pre_topc(X47,X46)
      | m1_pre_topc(X47,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_34,plain,(
    ! [X27,X28,X29] :
      ( ( ~ m1_connsp_2(X29,X27,X28)
        | r2_hidden(X28,k1_tops_1(X27,X29))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r2_hidden(X28,k1_tops_1(X27,X29))
        | m1_connsp_2(X29,X27,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk7_0,k1_tops_1(esk5_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24])])).

cnf(c_0_37,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk8_0,k1_tops_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_38])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_46,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X34)
      | ~ m1_pre_topc(X37,X34)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
      | ~ m1_pre_topc(X37,X36)
      | k3_tmap_1(X34,X35,X36,X37,X38) = k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),X38,u1_struct_0(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_47,plain,(
    ! [X30,X31,X32,X33] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
      | ~ m1_pre_topc(X33,X30)
      | k2_tmap_1(X30,X31,X32,X33) = k2_partfun1(u1_struct_0(X30),u1_struct_0(X31),X32,u1_struct_0(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_48,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
      | v2_struct_0(X42)
      | ~ m1_pre_topc(X42,X40)
      | ~ m1_subset_1(X43,u1_struct_0(X40))
      | ~ m1_subset_1(X44,u1_struct_0(X42))
      | X43 != X44
      | ~ r1_tmap_1(X40,X39,X41,X43)
      | r1_tmap_1(X42,X39,k2_tmap_1(X40,X39,X41,X42),X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

fof(c_0_49,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | m1_subset_1(X23,u1_struct_0(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_50,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X7,X1,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ r1_tarski(X7,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_51,negated_conjecture,
    ( m1_connsp_2(esk7_0,esk5_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_24]),c_0_43]),c_0_25]),c_0_44])]),c_0_45])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk5_0,X1,X2,esk8_0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X3,X1,esk5_0,X4,X2),esk8_0)
    | ~ v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_subset_1(esk8_0,u1_struct_0(X4))
    | ~ m1_pre_topc(esk5_0,X3)
    | ~ m1_pre_topc(X4,esk5_0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ r1_tarski(esk7_0,u1_struct_0(X4)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24]),c_0_43])]),c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)
    | r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_52,c_0_40])).

cnf(c_0_67,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X1)) = k2_tmap_1(esk5_0,esk3_0,esk6_0,X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_25]),c_0_58]),c_0_44])]),c_0_59]),c_0_45])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,esk3_0,k3_tmap_1(X2,esk3_0,esk5_0,X1,esk6_0),esk8_0)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r1_tarski(esk7_0,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_76,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_77,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk5_0,esk3_0,esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)
    | ~ r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_79,negated_conjecture,
    ( r1_tmap_1(X1,esk3_0,k2_tmap_1(esk5_0,esk3_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_54]),c_0_55]),c_0_56]),c_0_25]),c_0_57]),c_0_44]),c_0_58])]),c_0_59]),c_0_45])).

cnf(c_0_80,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_18]),c_0_68]),c_0_19]),c_0_38]),c_0_73])]),c_0_74]),c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,esk4_0,esk6_0) = k2_tmap_1(esk5_0,esk3_0,esk6_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_68]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_64])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(X1,esk3_0,k2_tmap_1(esk5_0,esk3_0,esk6_0,X1),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( k2_tmap_1(esk5_0,esk3_0,esk6_0,esk4_0) = k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_18]),c_0_19]),c_0_38])]),c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_80])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_68]),c_0_84]),c_0_72])]),c_0_85]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.030 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t84_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.13/0.39  fof(t83_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>(((r1_tarski(X6,u1_struct_0(X3))&m1_connsp_2(X6,X4,X7))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 0.13/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.39  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.13/0.39  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.13/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.39  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.13/0.39  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.13/0.39  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t84_tmap_1])).
% 0.13/0.39  fof(c_0_14, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|l1_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk4_0))&((((v3_pre_topc(esk7_0,esk5_0)&r2_hidden(esk8_0,esk7_0))&r1_tarski(esk7_0,u1_struct_0(esk4_0)))&esk8_0=esk9_0)&((~r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0))&(r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.39  fof(c_0_16, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~v3_pre_topc(X25,X24)|~r1_tarski(X25,X26)|r1_tarski(X25,k1_tops_1(X24,X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.13/0.39  cnf(c_0_17, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_20, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  fof(c_0_21, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  cnf(c_0_22, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.13/0.39  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (r1_tarski(esk7_0,k1_tops_1(esk5_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.13/0.39  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.13/0.39  fof(c_0_31, plain, ![X17, X18]:(~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|v2_pre_topc(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.13/0.39  fof(c_0_32, plain, ![X48, X49, X50, X51, X52, X53, X54, X55]:((~r1_tmap_1(X51,X49,X52,X54)|r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)|(~r1_tarski(X53,u1_struct_0(X50))|~m1_connsp_2(X53,X51,X54)|X54!=X55)|~m1_subset_1(X55,u1_struct_0(X50))|~m1_subset_1(X54,u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|~m1_pre_topc(X50,X51)|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49)))))|(v2_struct_0(X51)|~m1_pre_topc(X51,X48))|(v2_struct_0(X50)|~m1_pre_topc(X50,X48))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(~r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)|r1_tmap_1(X51,X49,X52,X54)|(~r1_tarski(X53,u1_struct_0(X50))|~m1_connsp_2(X53,X51,X54)|X54!=X55)|~m1_subset_1(X55,u1_struct_0(X50))|~m1_subset_1(X54,u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|~m1_pre_topc(X50,X51)|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49)))))|(v2_struct_0(X51)|~m1_pre_topc(X51,X48))|(v2_struct_0(X50)|~m1_pre_topc(X50,X48))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_tmap_1])])])])])).
% 0.13/0.39  fof(c_0_33, plain, ![X45, X46, X47]:(~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_pre_topc(X46,X45)|(~m1_pre_topc(X47,X46)|m1_pre_topc(X47,X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.39  fof(c_0_34, plain, ![X27, X28, X29]:((~m1_connsp_2(X29,X27,X28)|r2_hidden(X28,k1_tops_1(X27,X29))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~r2_hidden(X28,k1_tops_1(X27,X29))|m1_connsp_2(X29,X27,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk8_0,X1)|~r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(esk7_0,k1_tops_1(esk5_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24])])).
% 0.13/0.39  cnf(c_0_37, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_39, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~r1_tarski(X8,u1_struct_0(X1))|~m1_connsp_2(X8,X4,X7)|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_40, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  cnf(c_0_41, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk8_0,k1_tops_1(esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19]), c_0_38])])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_46, plain, ![X34, X35, X36, X37, X38]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_pre_topc(X36,X34)|(~m1_pre_topc(X37,X34)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))|(~m1_pre_topc(X37,X36)|k3_tmap_1(X34,X35,X36,X37,X38)=k2_partfun1(u1_struct_0(X36),u1_struct_0(X35),X38,u1_struct_0(X37)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.13/0.39  fof(c_0_47, plain, ![X30, X31, X32, X33]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))|(~m1_pre_topc(X33,X30)|k2_tmap_1(X30,X31,X32,X33)=k2_partfun1(u1_struct_0(X30),u1_struct_0(X31),X32,u1_struct_0(X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.39  fof(c_0_48, plain, ![X39, X40, X41, X42, X43, X44]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X40)|(~m1_subset_1(X43,u1_struct_0(X40))|(~m1_subset_1(X44,u1_struct_0(X42))|(X43!=X44|~r1_tmap_1(X40,X39,X41,X43)|r1_tmap_1(X42,X39,k2_tmap_1(X40,X39,X41,X42),X44)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.13/0.39  fof(c_0_49, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~m1_pre_topc(X22,X21)|(~m1_subset_1(X23,u1_struct_0(X22))|m1_subset_1(X23,u1_struct_0(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.13/0.39  cnf(c_0_50, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X7,X1,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~r1_tarski(X7,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_39, c_0_40])])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (m1_connsp_2(esk7_0,esk5_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_24]), c_0_43]), c_0_25]), c_0_44])]), c_0_45])).
% 0.13/0.39  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_60, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  cnf(c_0_61, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk5_0,X1,X2,esk8_0)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|~r1_tmap_1(X4,X1,k3_tmap_1(X3,X1,esk5_0,X4,X2),esk8_0)|~v1_funct_2(X2,u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_subset_1(esk8_0,u1_struct_0(X4))|~m1_pre_topc(esk5_0,X3)|~m1_pre_topc(X4,esk5_0)|~l1_pre_topc(X3)|~l1_pre_topc(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X1)|~r1_tarski(esk7_0,u1_struct_0(X4))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_24]), c_0_43])]), c_0_45])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_66, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_52, c_0_40])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X1))=k2_tmap_1(esk5_0,esk3_0,esk6_0,X1)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_25]), c_0_58]), c_0_44])]), c_0_59]), c_0_45])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_69, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]), c_0_61])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,esk3_0,k3_tmap_1(X2,esk3_0,esk5_0,X1,esk6_0),esk8_0)|~m1_subset_1(esk8_0,u1_struct_0(X1))|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X1,esk5_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~r1_tarski(esk7_0,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])]), c_0_59])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)|r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_65, c_0_64])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])]), c_0_59])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=k2_tmap_1(esk5_0,esk3_0,esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (~r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (r1_tmap_1(X1,esk3_0,k2_tmap_1(esk5_0,esk3_0,esk6_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk5_0,esk3_0,esk6_0,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_54]), c_0_55]), c_0_56]), c_0_25]), c_0_57]), c_0_44]), c_0_58])]), c_0_59]), c_0_45])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_18]), c_0_68]), c_0_19]), c_0_38]), c_0_73])]), c_0_74]), c_0_75])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,esk4_0,esk6_0)=k2_tmap_1(esk5_0,esk3_0,esk6_0,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_68]), c_0_77])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (~r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)|~r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_78, c_0_64])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (r1_tmap_1(X1,esk3_0,k2_tmap_1(esk5_0,esk3_0,esk6_0,X1),esk8_0)|v2_struct_0(X1)|~m1_subset_1(esk8_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (k2_tmap_1(esk5_0,esk3_0,esk6_0,esk4_0)=k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_18]), c_0_19]), c_0_38])]), c_0_75])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (~r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_80])])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_68]), c_0_84]), c_0_72])]), c_0_85]), c_0_74]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 87
% 0.13/0.39  # Proof object clause steps            : 60
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 47
% 0.13/0.39  # Proof object clause conjectures      : 44
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 34
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 18
% 0.13/0.39  # Proof object simplifying inferences  : 80
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 41
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 41
% 0.13/0.39  # Processed clauses                    : 133
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 3
% 0.13/0.39  # ...remaining for further processing  : 128
% 0.13/0.39  # Other redundant clauses eliminated   : 5
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 5
% 0.13/0.39  # Generated clauses                    : 62
% 0.13/0.39  # ...of the previous two non-trivial   : 53
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 57
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
% 0.13/0.39  # Current number of processed clauses  : 78
% 0.13/0.39  #    Positive orientable unit clauses  : 30
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 5
% 0.13/0.39  #    Non-unit-clauses                  : 43
% 0.13/0.39  # Current number of unprocessed clauses: 1
% 0.13/0.39  # ...number of literals in the above   : 20
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 45
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 2191
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 140
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 7
% 0.13/0.39  # Unit Clause-clause subsumption calls : 24
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 9
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 6999
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.040 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.045 s
% 0.13/0.39  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
